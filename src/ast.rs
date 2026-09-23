// src/ast.rs
// Abstract Syntax Tree definitions and pest-pair lowering for the Fire language.

use std::fmt;

// ---------------------------------------------------------------------------
// AST types
// ---------------------------------------------------------------------------

/// Top-level AST node representing a Fire program
#[derive(Debug, Clone, PartialEq)]
pub struct Program {
    pub statements: Vec<Stmt>,
}

/// A statement together with its source line (1-based), for error reporting.
#[derive(Debug, Clone, PartialEq)]
pub struct Stmt {
    pub node: Statement,
    pub line: usize,
}

/// A statement in the Fire language
#[derive(Debug, Clone, PartialEq)]
pub enum Statement {
    Documentation(String),
    Comment(String),
    /// `public var x = ...` — creates a new binding (and possibly an object property).
    Declaration {
        is_public: bool,
        is_mutable: bool,
        pattern: Pattern,
        value: Expression,
    },
    /// `a = b = expr`, `x += 1`, `{key, value} = entry`, `self.{...} = parent`, ...
    Assignment {
        targets: Vec<(Pattern, AssignmentOp)>,
        value: Expression,
    },
    Return(Option<Expression>),
    Break,
    Continue,
    While {
        condition: Expression,
        body: Vec<Stmt>,
    },
    For {
        /// The loop target: an identifier or a destructuring pattern, or
        /// (for `for a, b in xs, ys`) a list pattern built from the comma
        /// list, one target per iterable.
        pattern: Pattern,
        /// More than one iterable runs in lockstep; the targets take one
        /// current value each.
        iterables: Vec<Expression>,
        body: Vec<Stmt>,
    },
    If {
        condition: Expression,
        body: Vec<Stmt>,
        elif_branches: Vec<(Expression, Vec<Stmt>)>,
        else_body: Option<Vec<Stmt>>,
    },
    Match {
        subject: Expression,
        arms: Vec<MatchArm>,
    },
    /// `def name(params) <block>` — named function / constructor.
    /// `unsafe def` skips the termination check.
    Def {
        is_public: bool,
        is_unsafe: bool,
        name: String,
        params: Vec<Param>,
        return_type: Option<Expression>,
        body: Vec<Stmt>,
    },
    /// `type Name` with one constructor per line.
    TypeDecl {
        name: String,
        ctors: Vec<CtorDecl>,
    },
    /// `law name` with quantified variables, an optional hypothesis and a
    /// claim.
    Law {
        name: String,
        vars: Vec<(String, Expression)>,
        hyp: Option<Expression>,
        claim: Expression,
    },
    Expression(Expression),
}

/// One constructor of a `type` declaration: a name and its fields, each
/// with an optional type (an untyped field is a type parameter).
#[derive(Debug, Clone, PartialEq)]
pub struct CtorDecl {
    pub name: String,
    pub fields: Vec<(String, Option<Expression>)>,
}

/// One arm of a `match` block: `pattern => body`.
#[derive(Debug, Clone, PartialEq)]
pub struct MatchArm {
    pub pattern: Pattern,
    /// `pattern if cond => ...` — the arm matches only when the guard is truthy
    pub guard: Option<Expression>,
    pub body: Expression,
    pub line: usize,
}

/// A function/lambda parameter.
#[derive(Debug, Clone, PartialEq)]
pub struct Param {
    pub is_public: bool,
    /// `var` parameter: the binding (and the member, if public) is mutable.
    pub is_var: bool,
    pub pattern: Pattern,
    pub default: Option<Expression>,
}

/// Patterns: the left-hand side of `=`, function parameters, and match arms.
#[derive(Debug, Clone, PartialEq)]
pub enum Pattern {
    /// `x` — binds (always matches)
    Identifier(String),
    /// `pattern: type` — runtime type check
    Typed {
        pattern: Box<Pattern>,
        type_expr: Expression,
    },
    /// Literal pattern (numbers, strings, booleans, nothing) — matches by equality
    Literal(Expression),
    /// `[a, b, ...rest]`
    List(Vec<Pattern>),
    /// `...rest` / `...` inside a list pattern
    Rest(Option<String>),
    /// `{key, other: pattern}`
    Object(Vec<(String, Pattern)>),
    /// `Node(l, v, r)` — a constructor with positional sub-patterns
    Ctor(String, Vec<Pattern>),
    /// `"{h}:{m}"` — string destructuring
    FString(Vec<FStringPart>),
    /// `obj.member = ...` (assignment only)
    Member {
        object: Expression,
        member: String,
    },
    /// `obj[index] = ...` (assignment only)
    Index {
        object: Expression,
        index: Expression,
    },
    /// `self.{...} = parent` — copy public members into an object (assignment only)
    SpreadInto { object: Expression },
}

/// Assignment operators
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum AssignmentOp {
    Assign,
    AddAssign,
    SubAssign,
    MulAssign,
    DivAssign,
    ModAssign,
    PowAssign,
    BitAndAssign,
    BitOrAssign,
    BitXorAssign,
    ShlAssign,
    ShrAssign,
    UShrAssign,
}

impl AssignmentOp {
    pub fn from_str(s: &str) -> Option<AssignmentOp> {
        Some(match s {
            "=" => AssignmentOp::Assign,
            "+=" => AssignmentOp::AddAssign,
            "-=" => AssignmentOp::SubAssign,
            "*=" => AssignmentOp::MulAssign,
            "/=" => AssignmentOp::DivAssign,
            "%=" => AssignmentOp::ModAssign,
            "**=" => AssignmentOp::PowAssign,
            "&=" => AssignmentOp::BitAndAssign,
            "|=" => AssignmentOp::BitOrAssign,
            "^=" => AssignmentOp::BitXorAssign,
            "<<=" => AssignmentOp::ShlAssign,
            ">>=" => AssignmentOp::ShrAssign,
            ">>>=" => AssignmentOp::UShrAssign,
            _ => return None,
        })
    }
}

/// Expressions in the Fire language
#[derive(Debug, Clone, PartialEq)]
pub enum Expression {
    // Literals
    Identifier(String),
    Import(String),
    Number(NumberLiteral),
    Str(String),
    FString(Vec<FStringPart>),
    TString(String),
    Boolean(bool),
    Nothing,
    Ellipsis,
    /// `$` — the piped value inside a pipeline RHS
    PreviousResult,

    // Collections
    List(Vec<Expression>),
    Object(Vec<ObjectEntry>),

    // Operations
    BinaryOp {
        left: Box<Expression>,
        op: BinaryOperator,
        right: Box<Expression>,
    },
    UnaryOp {
        op: UnaryOperator,
        operand: Box<Expression>,
    },

    // Functions
    Lambda {
        params: Vec<Param>,
        body: Box<Expression>,
    },
    /// An indented block used as an expression (lambda bodies, assignment RHS).
    /// Evaluates to the value of its last statement.
    Block(Vec<Stmt>),
    Call {
        function: Box<Expression>,
        args: Vec<Expression>,
        /// `f(width = 3)` — arguments passed by parameter name
        named_args: Vec<(String, Expression)>,
    },

    // Access
    MemberAccess {
        object: Box<Expression>,
        member: String,
    },
    /// `expr.{...}` — only valid as an assignment target
    SpreadMember { object: Box<Expression> },
    Index {
        object: Box<Expression>,
        index: Box<Expression>,
    },

    // Control flow expressions
    IfExpr {
        condition: Box<Expression>,
        then_branch: Box<Expression>,
        elif_branches: Vec<(Expression, Expression)>,
        else_branch: Option<Box<Expression>>,
    },
    /// `for x in xs do expr` / `while cond do expr` used as an expression;
    /// produces the list of body values (an `if` body without `else` filters).
    Comprehension {
        clauses: Vec<CompClause>,
        body: Box<Expression>,
    },

    // Type-related
    TypeCheck {
        expression: Box<Expression>,
        type_expr: Box<Expression>,
    },

    // Other
    Range {
        start: Option<Box<Expression>>,
        end: Option<Box<Expression>>,
    },
    Pipeline {
        left: Box<Expression>,
        op: PipelineOperator,
        right: Box<Expression>,
    },
}

/// A clause of a comprehension expression.
#[derive(Debug, Clone, PartialEq)]
pub enum CompClause {
    For { pattern: Pattern, iterables: Vec<Expression> },
}

/// Parts of an f-string
#[derive(Debug, Clone, PartialEq)]
pub enum FStringPart {
    Text(String),
    /// `{expr}` or `{expr:spec}`, with the spec's text after the `:`
    Expression(Expression, Option<String>),
}

/// A format spec, `[[fill]align][0][width][.precision][f|d]`.
#[derive(Debug, Clone, PartialEq)]
pub struct FormatSpec {
    pub fill: char,
    /// `<`, `>` or `^`, when given
    pub align: Option<char>,
    /// a `0` before the width: pad a number with zeros after its sign
    pub zeros: bool,
    pub width: u32,
    /// digits after the point, with `.n` or `f` (six by default)
    pub precision: Option<u32>,
}

impl FormatSpec {
    pub fn parse(spec: &str) -> Option<FormatSpec> {
        let chars: Vec<char> = spec.chars().collect();
        let is_align = |c: &char| matches!(c, '<' | '>' | '^');
        let (fill, align, mut rest) = match chars.as_slice() {
            [f, a, rest @ ..] if is_align(a) => (*f, Some(*a), rest),
            [a, rest @ ..] if is_align(a) => (' ', Some(*a), rest),
            rest => (' ', None, rest),
        };
        let zeros = rest.len() > 1 && rest[0] == '0' && rest[1].is_ascii_digit();
        let digits = |rest: &mut &[char]| -> Option<u32> {
            let n = rest.iter().take_while(|c| c.is_ascii_digit()).count();
            let (d, tail) = rest.split_at(n);
            *rest = tail;
            if n == 0 { None } else { d.iter().collect::<String>().parse().ok() }
        };
        let width = digits(&mut rest).unwrap_or(0);
        let mut precision = None;
        if let ['.', tail @ ..] = rest {
            rest = tail;
            precision = Some(digits(&mut rest)?);
        }
        match rest {
            [] | ['d'] if precision.is_none() || rest.is_empty() => {}
            ['f'] => precision = precision.or(Some(6)),
            _ => return None,
        }
        Some(FormatSpec { fill, align, zeros, width, precision })
    }
}

/// Object entry
#[derive(Debug, Clone, PartialEq)]
pub enum ObjectEntry {
    KeyValue { key: String, value: Expression },
    Shorthand(String),
    Spread,
}

/// Number literal types (kept as source text; converted by the interpreter)
#[derive(Debug, Clone, PartialEq)]
pub enum NumberLiteral {
    Decimal(String),
    Hex(String),
    Binary(String),
    Scientific(String),
}

/// Binary operators
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum BinaryOperator {
    Add, Sub, Mul, Div, Mod, Pow,
    Eq, Ne, Lt, Le, Gt, Ge,
    And, Or,
    /// `|` and `&`: a union / intersection in a type, bitwise or / and on ints
    TypeOr, TypeAnd,
    /// `>>` keeps the sign, `>>>` shifts in zeros
    BitXor, Shl, Shr, UShr,
}

/// Unary operators
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum UnaryOperator {
    Plus, Minus, Not, Spread,
}

/// Pipeline operators
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum PipelineOperator {
    Pipe,   // |>
    Map,    // *>
    Filter, // ?>
    Handle, // !> — runs only on the error channel
}

// ---------------------------------------------------------------------------
// Errors
// ---------------------------------------------------------------------------

/// Error during AST construction (lowering from pest pairs).
#[derive(Debug, Clone, PartialEq)]
pub struct SemanticError {
    pub message: String,
    pub position: Option<(usize, usize)>,
}

impl SemanticError {
    fn new(message: impl Into<String>, position: Option<(usize, usize)>) -> Self {
        SemanticError { message: message.into(), position }
    }
}

impl fmt::Display for SemanticError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.message)?;
        if let Some((line, col)) = self.position {
            write!(f, " (line {}, column {})", line, col)?;
        }
        Ok(())
    }
}

impl std::error::Error for SemanticError {}

/// Result type for AST operations
pub type Result<T> = std::result::Result<T, SemanticError>;

type Pair<'a> = pest::iterators::Pair<'a, crate::Rule>;

fn err<T>(pair: &Pair<'_>, msg: impl Into<String>) -> Result<T> {
    Err(SemanticError::new(msg, Some(pair.line_col())))
}

// ---------------------------------------------------------------------------
// Lowering: pest pairs -> AST
// ---------------------------------------------------------------------------

use crate::Rule;

/// Convert pest pairs to AST
pub fn from_pest_pairs(mut pairs: pest::iterators::Pairs<'_, crate::Rule>) -> std::result::Result<Program, Box<dyn std::error::Error>> {
    let program_pair = pairs.next().ok_or("No program rule found")?;

    if program_pair.as_rule() != Rule::program {
        return Err(format!("Expected program rule, got {:?}", program_pair.as_rule()).into());
    }

    let mut statements = Vec::new();
    for pair in program_pair.into_inner() {
        match pair.as_rule() {
            Rule::statement => statements.push(parse_statement(pair)?),
            Rule::EOI => break,
            other => {
                return Err(SemanticError::new(
                    format!("unexpected top-level rule {:?}", other),
                    Some(pair.line_col()),
                ).into());
            }
        }
    }

    Ok(Program { statements })
}

/// `return`, `break` or `continue` as the body of an arm or lambda.
fn parse_control(pair: Pair<'_>) -> Result<Stmt> {
    let line = pair.line_col().0;
    let node = match pair.as_rule() {
        Rule::return_stmt => parse_return_statement(pair)?,
        Rule::break_stmt => Statement::Break,
        Rule::continue_stmt => Statement::Continue,
        other => return err(&pair, format!("unexpected rule {:?} as a control statement", other)),
    };
    Ok(Stmt { node, line })
}

fn parse_statement(pair: Pair<'_>) -> Result<Stmt> {
    let line = pair.line_col().0;
    let mut inner = pair.into_inner().peekable();
    let first = match inner.next() {
        Some(p) => p,
        None => return Ok(Stmt { node: Statement::Comment(String::new()), line }),
    };

    let node = match first.as_rule() {
        Rule::documentation => {
            Statement::Documentation(first.as_str().trim_start_matches('#').trim().to_string())
        }
        Rule::comment => {
            Statement::Comment(first.as_str().trim_start_matches('#').trim().to_string())
        }
        Rule::variable_declaration => parse_variable_declaration(first)?,
        Rule::assignment_stmt => parse_assignment_statement(first)?,
        Rule::return_stmt => parse_return_statement(first)?,
        Rule::break_stmt => Statement::Break,
        Rule::continue_stmt => Statement::Continue,
        Rule::while_stmt => parse_while_statement(first)?,
        Rule::for_stmt => parse_for_statement(first)?,
        Rule::if_stmt => parse_if_statement(first)?,
        Rule::match_stmt => parse_match_statement(first)?,
        Rule::guarded_arm => {
            return err(&first, "`pattern if condition => ...` is only valid as a match arm");
        }
        Rule::method_stmt => parse_def_statement(first)?,
        Rule::type_stmt => parse_type_statement(first)?,
        Rule::law_stmt => parse_law_statement(first)?,
        Rule::pipeline_expr => Statement::Expression(parse_expression(first)?),
        other => return err(&first, format!("unhandled statement rule {:?}", other)),
    };

    Ok(Stmt { node, line })
}

/// Parse the remaining pairs of a statement body: either a single expression
/// pair (`pipeline_expr`) or a sequence of `statement` pairs (an inlined block).
fn parse_value_or_block<'a>(pairs: impl Iterator<Item = Pair<'a>>) -> Result<Expression> {
    let mut stmts = Vec::new();
    let mut expr = None;
    for p in pairs {
        match p.as_rule() {
            Rule::pipeline_expr if expr.is_none() && stmts.is_empty() => {
                expr = Some(parse_expression(p)?);
            }
            Rule::match_stmt if expr.is_none() && stmts.is_empty() => {
                // `x = match subject ...` — a match used as a value
                let line = p.line_col().0;
                let node = parse_match_statement(p)?;
                expr = Some(Expression::Block(vec![Stmt { node, line }]));
            }
            Rule::statement => stmts.push(parse_statement(p)?),
            Rule::comment => {}
            other => return err(&p, format!("unexpected rule {:?} in value position", other)),
        }
    }
    match (expr, stmts.is_empty()) {
        (Some(e), _) => Ok(e),
        (None, false) => Ok(Expression::Block(stmts)),
        (None, true) => Ok(Expression::Nothing),
    }
}

fn parse_variable_declaration(pair: Pair<'_>) -> Result<Statement> {
    let mut is_public = false;
    let mut is_mutable = false;
    let mut pattern = None;
    let mut rest = Vec::new();

    for inner in pair.into_inner() {
        match inner.as_rule() {
            Rule::kw_public => is_public = true,
            Rule::kw_var => is_mutable = true,
            Rule::typecheck if pattern.is_none() => {
                pattern = Some(expression_to_pattern(parse_expression(inner.clone())?, &inner)?);
            }
            _ => rest.push(inner),
        }
    }

    let pattern = pattern.ok_or_else(|| SemanticError::new("declaration without target", None))?;
    let value = parse_value_or_block(rest.into_iter())?;

    Ok(Statement::Declaration { is_public, is_mutable, pattern, value })
}

fn parse_assignment_statement(pair: Pair<'_>) -> Result<Statement> {
    let mut targets: Vec<(Pattern, AssignmentOp)> = Vec::new();
    let mut pending: Option<Pattern> = None;
    let mut rest = Vec::new();

    for inner in pair.into_inner() {
        match inner.as_rule() {
            Rule::typecheck if rest.is_empty() => {
                if let Some(p) = pending.take() {
                    // shouldn't happen (op always follows target), but be safe
                    targets.push((p, AssignmentOp::Assign));
                }
                pending = Some(expression_to_pattern(parse_expression(inner.clone())?, &inner)?);
            }
            Rule::assignment_op => {
                let op = match AssignmentOp::from_str(inner.as_str()) {
                    Some(op) => op,
                    None => return err(&inner, format!("unknown assignment operator '{}'", inner.as_str())),
                };
                match pending.take() {
                    Some(p) => targets.push((p, op)),
                    None => return err(&inner, "assignment operator without target"),
                }
            }
            _ => rest.push(inner),
        }
    }
    if let Some(p) = pending {
        targets.push((p, AssignmentOp::Assign));
    }

    let value = parse_value_or_block(rest.into_iter())?;
    Ok(Statement::Assignment { targets, value })
}

fn parse_return_statement(pair: Pair<'_>) -> Result<Statement> {
    let rest: Vec<_> = pair.into_inner().filter(|p| p.as_rule() != Rule::kw_return).collect();
    if rest.is_empty() {
        Ok(Statement::Return(None))
    } else {
        Ok(Statement::Return(Some(parse_value_or_block(rest.into_iter())?)))
    }
}

/// Collect a `do`-expression or inlined block statements from the tail of a
/// while/for statement.
fn parse_loop_tail<'a>(pairs: impl Iterator<Item = Pair<'a>>) -> Result<Vec<Stmt>> {
    let mut body = Vec::new();
    let mut saw_do = false;

    for p in pairs {
        match p.as_rule() {
            Rule::kw_do => saw_do = true,
            Rule::assignment_expr | Rule::pipeline_expr_simple if saw_do => {
                let line = p.line_col().0;
                body.push(Stmt { node: Statement::Expression(parse_expression(p)?), line });
            }
            Rule::break_stmt if saw_do => {
                body.push(Stmt { node: Statement::Break, line: p.line_col().0 });
            }
            Rule::continue_stmt if saw_do => {
                body.push(Stmt { node: Statement::Continue, line: p.line_col().0 });
            }
            Rule::return_stmt if saw_do => {
                let line = p.line_col().0;
                body.push(Stmt { node: parse_return_statement(p)?, line });
            }
            Rule::statement => body.push(parse_statement(p)?),
            other => return err(&p, format!("unexpected rule {:?} in loop body", other)),
        }
    }

    Ok(body)
}

fn parse_while_statement(pair: Pair<'_>) -> Result<Statement> {
    let mut inner = pair.into_inner().peekable();
    // kw_while, condition, then tail
    expect_rule(&mut inner, Rule::kw_while)?;
    let cond_pair = inner.next().ok_or_else(|| SemanticError::new("while without condition", None))?;
    let condition = parse_expression(cond_pair)?;
    let body = parse_loop_tail(inner)?;
    Ok(Statement::While { condition, body })
}

fn parse_for_statement(pair: Pair<'_>) -> Result<Statement> {
    let mut inner = pair.into_inner().peekable();
    expect_rule(&mut inner, Rule::kw_for)?;
    let (pattern, iterables) = parse_for_header(&mut inner)?;
    let body = parse_loop_tail(inner)?;
    Ok(Statement::For { pattern, iterables, body })
}

/// The `targets in iterables` part of a for loop / comprehension clause:
/// consumes the target patterns (typecheck pairs), `in`, and the iterables.
/// A comma always means lockstep: comma-separated targets combine into one
/// list pattern, one target per iterable. Taking one item apart is a
/// pattern (`for {key, value} in d`).
fn parse_for_header<'a>(
    inner: &mut std::iter::Peekable<impl Iterator<Item = Pair<'a>>>,
) -> Result<(Pattern, Vec<Expression>)> {
    let mut targets = Vec::new();
    let mut at = None;
    loop {
        match inner.peek() {
            Some(p) if p.as_rule() == Rule::typecheck => {
                let p = inner.next().unwrap();
                at.get_or_insert(p.line_col());
                let expr = parse_expression(p.clone())?;
                targets.push(expression_to_pattern(expr, &p)?);
            }
            _ => break,
        }
    }
    if targets.is_empty() {
        return Err(SemanticError::new("for without a loop variable", None));
    }
    expect_rule(inner, Rule::kw_in)?;
    let mut iterables = Vec::new();
    while let Some(p) = inner.peek() {
        if p.as_rule() != Rule::pipeline_expr_simple {
            break;
        }
        iterables.push(parse_expression(inner.next().unwrap())?);
    }
    if iterables.is_empty() {
        return Err(SemanticError::new("for without an iterable", None));
    }
    if targets.len() > 1 && iterables.len() == 1 {
        return Err(SemanticError::new(
            format!("{} loop variables but 1 iterable: a comma in `for` goes through several iterables in lockstep (`for i, x in 0.., xs`); to take each item apart, use a pattern (`for {{key, value}} in d`, `for [a, b] in rows`)",
                targets.len()),
            at));
    }
    if targets.len() > 1 && targets.len() != iterables.len() {
        return Err(SemanticError::new(
            format!("{} loop variables but {} iterables: a loop in lockstep needs one iterable per variable",
                targets.len(), iterables.len()),
            at));
    }
    let pattern = if targets.len() == 1 {
        targets.pop().unwrap()
    } else {
        // `for a, b in xs, ys`: the current items, one per iterable
        Pattern::List(targets)
    };
    Ok((pattern, iterables))
}

fn expect_rule<'a>(
    iter: &mut std::iter::Peekable<impl Iterator<Item = Pair<'a>>>,
    rule: Rule,
) -> Result<Pair<'a>> {
    match iter.next() {
        Some(p) if p.as_rule() == rule => Ok(p),
        Some(p) => err(&p, format!("expected {:?}, found {:?}", rule, p.as_rule())),
        None => Err(SemanticError::new(format!("expected {:?}, found end of input", rule), None)),
    }
}

fn parse_if_statement(pair: Pair<'_>) -> Result<Statement> {
    let mut condition = None;
    let mut body = Vec::new();
    let mut elif_branches: Vec<(Expression, Vec<Stmt>)> = Vec::new();
    let mut else_body = None;

    // Sections: 0 = if, 1.. = elif. Keywords are visible, so track the section.
    enum Section { If, Elif }
    let mut section = Section::If;
    let mut saw_do = false;
    let mut current_cond: Option<Expression> = None;
    let mut current_body: Vec<Stmt> = Vec::new();

    for p in pair.into_inner() {
        match p.as_rule() {
            Rule::kw_if => {}
            Rule::kw_elif => {
                match section {
                    Section::If => {
                        body = std::mem::take(&mut current_body);
                    }
                    Section::Elif => {
                        let cond = current_cond.take()
                            .ok_or_else(|| SemanticError::new("elif without condition", Some(p.line_col())))?;
                        elif_branches.push((cond, std::mem::take(&mut current_body)));
                    }
                }
                section = Section::Elif;
                saw_do = false;
            }
            Rule::kw_do => saw_do = true,
            Rule::pipeline_expr_simple => {
                let line = p.line_col().0;
                current_body.push(Stmt { node: Statement::Expression(parse_expression(p)?), line });
            }
            Rule::assignment_expr => {
                let needs_cond = match section {
                    Section::If => condition.is_none(),
                    Section::Elif => current_cond.is_none(),
                };
                if needs_cond && !saw_do {
                    let cond = parse_expression(p)?;
                    match section {
                        Section::If => condition = Some(cond),
                        Section::Elif => current_cond = Some(cond),
                    }
                } else {
                    let line = p.line_col().0;
                    current_body.push(Stmt { node: Statement::Expression(parse_expression(p)?), line });
                }
            }
            Rule::break_stmt if saw_do => {
                current_body.push(Stmt { node: Statement::Break, line: p.line_col().0 });
            }
            Rule::continue_stmt if saw_do => {
                current_body.push(Stmt { node: Statement::Continue, line: p.line_col().0 });
            }
            Rule::return_stmt if saw_do => {
                let line = p.line_col().0;
                current_body.push(Stmt { node: parse_return_statement(p)?, line });
            }
            Rule::statement => current_body.push(parse_statement(p)?),
            Rule::r#else => {
                match section {
                    Section::If => body = std::mem::take(&mut current_body),
                    Section::Elif => {
                        let cond = current_cond.take()
                            .ok_or_else(|| SemanticError::new("elif without condition", Some(p.line_col())))?;
                        elif_branches.push((cond, std::mem::take(&mut current_body)));
                    }
                }
                section = Section::If; // avoid double-flush below
                else_body = Some(parse_else_clause(p)?);
            }
            other => return err(&p, format!("unexpected rule {:?} in if statement", other)),
        }
    }

    // Flush the last section.
    if !current_body.is_empty() || matches!(section, Section::Elif) {
        match section {
            Section::If => {
                if body.is_empty() {
                    body = current_body;
                }
            }
            Section::Elif => {
                if let Some(cond) = current_cond.take() {
                    elif_branches.push((cond, current_body));
                }
            }
        }
    }

    let condition = condition.ok_or_else(|| SemanticError::new("if without condition", None))?;
    Ok(Statement::If { condition, body, elif_branches, else_body })
}

fn parse_else_clause(pair: Pair<'_>) -> Result<Vec<Stmt>> {
    let mut statements = Vec::new();
    for p in pair.into_inner() {
        match p.as_rule() {
            Rule::kw_else => {}
            Rule::assignment_expr | Rule::pipeline_expr_simple => {
                let line = p.line_col().0;
                statements.push(Stmt { node: Statement::Expression(parse_expression(p)?), line });
            }
            Rule::statement => statements.push(parse_statement(p)?),
            other => return err(&p, format!("unexpected rule {:?} in else clause", other)),
        }
    }
    Ok(statements)
}

fn parse_match_statement(pair: Pair<'_>) -> Result<Statement> {
    let mut subject = None;
    let mut arms = Vec::new();

    for p in pair.into_inner() {
        match p.as_rule() {
            Rule::kw_match => {}
            Rule::assignment_expr => subject = Some(parse_expression(p)?),
            Rule::statement => {
                // a guarded arm (`pattern if cond => body`) is its own rule;
                // peek before generic statement parsing, which rejects it
                if let Some(inner) = p.clone().into_inner().next()
                    && inner.as_rule() == Rule::guarded_arm
                {
                    arms.push(parse_guarded_arm(inner)?);
                    continue;
                }
                let stmt = parse_statement(p.clone())?;
                match stmt.node {
                    Statement::Comment(_) | Statement::Documentation(_) => {}
                    Statement::Expression(Expression::Lambda { params, body }) => {
                        if params.len() != 1 {
                            return err(&p, format!(
                                "a match arm takes exactly one pattern, found {}", params.len()));
                        }
                        let param = params.into_iter().next().unwrap();
                        if param.default.is_some() {
                            return err(&p, "match arm patterns cannot have default values");
                        }
                        arms.push(MatchArm {
                            pattern: param.pattern,
                            guard: None,
                            body: *body,
                            line: stmt.line,
                        });
                    }
                    _ => {
                        return err(&p, "match blocks may only contain arms of the form `pattern => expression`");
                    }
                }
            }
            other => return err(&p, format!("unexpected rule {:?} in match statement", other)),
        }
    }

    let subject = subject.ok_or_else(|| SemanticError::new("match without subject", None))?;
    Ok(Statement::Match { subject, arms })
}

/// `pattern if condition => body` inside a match block.
fn parse_guarded_arm(pair: Pair<'_>) -> Result<MatchArm> {
    let line = pair.line_col().0;
    let src = pair.clone();
    let mut pattern = None;
    let mut guard = None;
    let mut body = None;
    let mut body_stmts: Vec<Stmt> = Vec::new();
    for p in pair.into_inner() {
        match p.as_rule() {
            Rule::kw_if | Rule::lambda_op => {}
            Rule::typecheck if pattern.is_none() => {
                pattern = Some(expression_to_pattern(parse_expression(p.clone())?, &p)?);
            }
            Rule::pipeline_expr if guard.is_some() => body = Some(parse_expression(p)?),
            Rule::return_stmt | Rule::break_stmt | Rule::continue_stmt => body_stmts.push(parse_control(p)?),
            // an indented block body arrives as individual statements
            Rule::statement => body_stmts.push(parse_statement(p)?),
            _ if guard.is_none() => guard = Some(parse_expression(p)?),
            other => {
                return err(&p, format!("unexpected rule {:?} in guarded match arm", other));
            }
        }
    }
    let body = match (body, body_stmts.is_empty()) {
        (Some(b), _) => b,
        (None, false) => Expression::Block(body_stmts),
        (None, true) => return err(&src, "guarded match arm without a body"),
    };
    match (pattern, guard) {
        (Some(pattern), Some(cond)) => Ok(MatchArm { pattern, guard: Some(cond), body, line }),
        _ => err(&src, "malformed guarded match arm"),
    }
}

/// `type Tree` with one constructor per line: `Leaf`, or
/// `Node(left: Tree, value, right: Tree)`.
fn parse_type_statement(pair: Pair<'_>) -> Result<Statement> {
    let src = pair.clone();
    let mut name = String::new();
    let mut ctors = Vec::new();
    for p in pair.into_inner() {
        match p.as_rule() {
            Rule::kw_type => {}
            Rule::identifier if name.is_empty() => name = p.as_str().to_string(),
            Rule::statement => {
                let line = p.clone();
                let stmt = parse_statement(p)?;
                match stmt.node {
                    Statement::Comment(_) | Statement::Documentation(_) => {}
                    Statement::Expression(Expression::Identifier(c)) => ctors.push(CtorDecl { name: c, fields: vec![] }),
                    Statement::Expression(Expression::Call { function, args, named_args }) => {
                        let c = match *function {
                            Expression::Identifier(c) => c,
                            _ => return err(&line, "a constructor is a name, optionally with fields in parentheses"),
                        };
                        if !named_args.is_empty() {
                            return err(&line, "constructor fields are `name` or `name: type`, not keyword arguments");
                        }
                        let mut fields = Vec::new();
                        for a in args {
                            match a {
                                Expression::Identifier(f) => fields.push((f, None)),
                                Expression::TypeCheck { expression, type_expr } => match *expression {
                                    Expression::Identifier(f) => fields.push((f, Some(*type_expr))),
                                    _ => return err(&line, "a constructor field is a name, optionally with a type"),
                                },
                                _ => return err(&line, "a constructor field is a name, optionally with a type"),
                            }
                        }
                        ctors.push(CtorDecl { name: c, fields });
                    }
                    _ => return err(&line, "a type declaration lists constructors, one per line"),
                }
            }
            other => return err(&p, format!("unexpected rule {:?} in type declaration", other)),
        }
    }
    if ctors.is_empty() {
        return err(&src, "a type needs at least one constructor");
    }
    Ok(Statement::TypeDecl { name, ctors })
}

/// `law name`, then optionally `for x: int, t: Tree if cond`, then the claim.
fn parse_law_statement(pair: Pair<'_>) -> Result<Statement> {
    let src = pair.clone();
    let mut name = String::new();
    let mut vars = Vec::new();
    let mut hyp = None;
    let mut claim = None;
    for p in pair.into_inner() {
        match p.as_rule() {
            Rule::kw_law | Rule::comment => {}
            Rule::identifier if name.is_empty() => name = p.as_str().to_string(),
            Rule::law_for => {
                for q in p.into_inner() {
                    match q.as_rule() {
                        Rule::kw_for | Rule::kw_if => {}
                        Rule::typecheck => {
                            let e = parse_expression(q.clone())?;
                            match e {
                                Expression::TypeCheck { expression, type_expr } => match *expression {
                                    Expression::Identifier(v) => vars.push((v, *type_expr)),
                                    _ => return err(&q, "a law variable is `name: type`"),
                                },
                                _ => return err(&q, "a law variable needs a type: `for x: int`"),
                            }
                        }
                        _ => hyp = Some(parse_expression(q)?),
                    }
                }
            }
            _ => claim = Some(parse_expression(p)?),
        }
    }
    let claim = claim.ok_or_else(|| SemanticError::new("a law needs a claim", Some(src.line_col())))?;
    Ok(Statement::Law { name, vars, hyp, claim })
}

fn parse_def_statement(pair: Pair<'_>) -> Result<Statement> {
    let mut is_public = false;
    let mut is_unsafe = false;
    let mut name = String::new();
    let mut params = Vec::new();
    let mut return_type = None;
    let mut body = Vec::new();
    let mut saw_type_op = false;

    for p in pair.into_inner() {
        match p.as_rule() {
            Rule::kw_public => is_public = true,
            Rule::kw_unsafe => is_unsafe = true,
            Rule::kw_def => {}
            Rule::identifier if name.is_empty() => name = p.as_str().to_string(),
            Rule::method_args => params = parse_def_params(p)?,
            Rule::typecheck_op => saw_type_op = true,
            Rule::logic_or if saw_type_op && return_type.is_none() => {
                return_type = Some(parse_expression(p)?);
            }
            Rule::statement => body.push(parse_statement(p)?),
            other => return err(&p, format!("unexpected rule {:?} in def", other)),
        }
    }

    Ok(Statement::Def { is_public, is_unsafe, name, params, return_type, body })
}

fn parse_def_params(pair: Pair<'_>) -> Result<Vec<Param>> {
    let mut params = Vec::new();
    let mut next_public = false;
    let mut next_var = false;

    for p in pair.into_inner() {
        match p.as_rule() {
            Rule::kw_public => next_public = true,
            Rule::kw_var => next_var = true,
            Rule::assignment_expr => {
                let mut param = parse_param_from_assignment_expr(p)?;
                param.is_public = next_public;
                param.is_var = next_var;
                next_public = false;
                next_var = false;
                params.push(param);
            }
            other => return err(&p, format!("unexpected rule {:?} in parameter list", other)),
        }
    }
    Ok(params)
}

/// A parameter comes in as an `assignment_expr` pair: `pattern` or `pattern = default`.
fn parse_param_from_assignment_expr(pair: Pair<'_>) -> Result<Param> {
    let src = pair.clone();
    let mut children: Vec<_> = pair.into_inner().collect();

    let (pattern_pair, default) = match children.len() {
        1 => (children.remove(0), None),
        3 => {
            let default_pair = children.pop().unwrap();
            let op = children.pop().unwrap();
            if op.as_str() != "=" {
                return err(&op, format!("only '=' is allowed for parameter defaults, found '{}'", op.as_str()));
            }
            (children.remove(0), Some(parse_expression(default_pair)?))
        }
        _ => return err(&src, "invalid parameter"),
    };

    let expr = parse_expression(pattern_pair.clone())?;
    let pattern = expression_to_pattern(expr, &pattern_pair)?;
    Ok(Param { is_public: false, is_var: false, pattern, default })
}

// ---------------------------------------------------------------------------
// Expressions
// ---------------------------------------------------------------------------

fn parse_expression(pair: Pair<'_>) -> Result<Expression> {
    // The precedence tower costs ~30 native frames per source nesting level;
    // grow the stack on demand so deeply nested expressions can't overflow it
    // (same guard as call_function in the interpreter).
    #[cfg(not(target_arch = "wasm32"))]
    {
        stacker::maybe_grow(64 * 1024, 1024 * 1024, || parse_expression_inner(pair))
    }
    #[cfg(target_arch = "wasm32")]
    {
        parse_expression_inner(pair)
    }
}

fn parse_expression_inner(pair: Pair<'_>) -> Result<Expression> {
    match pair.as_rule() {
        // --- atoms ---
        Rule::identifier => Ok(Expression::Identifier(pair.as_str().to_string())),
        Rule::import => Ok(Expression::Import(pair.as_str().trim_start_matches('$').to_string())),
        Rule::number => parse_number_literal(pair),
        Rule::string => {
            let s = pair.as_str();
            Ok(Expression::Str(s[1..s.len() - 1].to_string()))
        }
        Rule::fstring => Ok(Expression::FString(parse_fstring_parts(pair)?)),
        Rule::tstring => {
            let s = pair.as_str();
            Ok(Expression::TString(s[1..s.len() - 1].to_string()))
        }
        Rule::boolean => Ok(Expression::Boolean(pair.as_str() == "true")),
        Rule::nothing_lit => Ok(Expression::Nothing),
        Rule::ellipsis => Ok(Expression::Ellipsis),
        Rule::previous_result => Ok(Expression::PreviousResult),
        Rule::list => parse_list_literal(pair),
        Rule::object => parse_object_literal(pair),
        Rule::paren_expr => {
            let mut inner = pair.clone().into_inner();
            match (inner.next(), inner.next()) {
                (None, _) => Ok(Expression::Nothing),
                (Some(only), None) => parse_expression(only),
                // commas parse only so `(a, b) => ...` can be a parameter
                // list; anywhere else they are a mistake
                _ => err(&pair, "commas inside parentheses form a lambda parameter list \
                    (`(a, b) => ...`); for a sequence value use a list `[a, b]`"),
            }
        }

        // --- expression chain ---
        Rule::pipeline_expr => parse_pipeline(pair),
        Rule::pipeline_expr_simple => {
            // A pipeline chain without a continuation block.
            let open = open_lambdas(&pair);
            let mut links = Vec::new();
            flatten_pipeline_simple(pair, &mut links)?;
            build_pipeline_in_lambda(links, open)
        }
        Rule::lambda_expr => parse_lambda_expression(pair),
        Rule::loop_expr => parse_loop_expression(pair),
        Rule::if_expr => parse_if_expression(pair),
        Rule::assignment_expr => {
            let src = pair.clone();
            let line = src.line_col().0;
            let mut children: Vec<_> = pair.into_inner().collect();
            if children.len() == 1 {
                parse_expression(children.into_iter().next().unwrap())
            } else {
                // An assignment used in expression position (e.g. a lambda body
                // `() => count += 1`) is sugar for a one-statement block.
                if children.len() % 2 == 0 {
                    return err(&src, "malformed assignment expression");
                }
                let value_pair = children.pop().unwrap();
                let value = parse_expression(value_pair)?;
                let mut targets = Vec::new();
                let mut iter = children.into_iter();
                while let (Some(target_pair), Some(op_pair)) = (iter.next(), iter.next()) {
                    let target = expression_to_pattern(parse_expression(target_pair.clone())?, &target_pair)?;
                    let op = match AssignmentOp::from_str(op_pair.as_str()) {
                        Some(op) => op,
                        None => return err(&op_pair, format!("unknown assignment operator '{}'", op_pair.as_str())),
                    };
                    targets.push((target, op));
                }
                Ok(Expression::Block(vec![Stmt {
                    node: Statement::Assignment { targets, value },
                    line,
                }]))
            }
        }
        Rule::logic_or => parse_binary_with_block(pair, Rule::logic_or_block),
        Rule::logic_or_simple => parse_binary_chain(pair, &[Rule::kw_or]),
        Rule::logic_and => parse_binary_with_block(pair, Rule::logic_and_block),
        Rule::logic_and_simple => parse_binary_chain(pair, &[Rule::kw_and]),
        Rule::logic_not => {
            let src = pair.clone();
            let mut negated = false;
            let mut result = None;
            for p in pair.into_inner() {
                match p.as_rule() {
                    Rule::kw_not => negated = true,
                    _ => result = Some(parse_expression(p)?),
                }
            }
            let expr = result.ok_or_else(|| SemanticError::new("empty logic_not", Some(src.line_col())))?;
            Ok(if negated {
                Expression::UnaryOp { op: UnaryOperator::Not, operand: Box::new(expr) }
            } else {
                expr
            })
        }
        Rule::comparison => parse_binary_with_block(pair, Rule::comparison_block),
        Rule::comparison_simple => parse_binary_chain(pair, &[Rule::comparison_op]),
        Rule::type_or => parse_binary_with_block(pair, Rule::type_or_block),
        Rule::type_or_simple => parse_binary_chain(pair, &[Rule::type_or_op]),
        Rule::xor => parse_binary_with_block(pair, Rule::xor_block),
        Rule::xor_simple => parse_binary_chain(pair, &[Rule::xor_op]),
        Rule::type_and => parse_binary_with_block(pair, Rule::type_and_block),
        Rule::type_and_simple => parse_binary_chain(pair, &[Rule::type_and_op]),
        Rule::range => parse_range_expression(pair),
        Rule::shift => parse_binary_with_block(pair, Rule::shift_block),
        Rule::shift_simple => parse_binary_chain(pair, &[Rule::shift_op]),
        Rule::additive => parse_binary_with_block(pair, Rule::additive_block),
        Rule::additive_simple => parse_binary_chain(pair, &[Rule::add_op]),
        Rule::multiplicative => parse_binary_with_block(pair, Rule::multiplicative_block),
        Rule::multiplicative_simple => parse_binary_chain(pair, &[Rule::mul_op]),
        Rule::unary => {
            let src = pair.clone();
            let mut op = None;
            let mut operand = None;
            for p in pair.into_inner() {
                match p.as_rule() {
                    Rule::unary_op => {
                        op = Some(match p.as_str() {
                            "+" => UnaryOperator::Plus,
                            "-" => UnaryOperator::Minus,
                            "..." => UnaryOperator::Spread,
                            other => return err(&p, format!("unknown unary operator '{}'", other)),
                        });
                    }
                    _ => operand = Some(parse_expression(p)?),
                }
            }
            let operand = operand.ok_or_else(|| SemanticError::new("empty unary", Some(src.line_col())))?;
            Ok(match op {
                Some(op) => Expression::UnaryOp { op, operand: Box::new(operand) },
                None => operand,
            })
        }
        Rule::power => {
            let src = pair.clone();
            let mut children: Vec<_> = pair.into_inner().collect();
            match children.len() {
                1 => parse_expression(children.remove(0)),
                3 => {
                    let right = parse_expression(children.pop().unwrap())?;
                    children.pop(); // power_op
                    let left = parse_expression(children.remove(0))?;
                    Ok(Expression::BinaryOp {
                        left: Box::new(left),
                        op: BinaryOperator::Pow,
                        right: Box::new(right),
                    })
                }
                _ => err(&src, "malformed power expression"),
            }
        }
        Rule::typecheck => parse_typecheck_expression(pair),
        Rule::call_or_access => {
            let mut inner = pair.into_inner();
            let simple = inner.next()
                .ok_or_else(|| SemanticError::new("empty call_or_access", None))?;
            let mut expr = parse_expression(simple)?;
            if let Some(block) = inner.next() {
                expr = apply_access_block(expr, block)?;
            }
            Ok(expr)
        }
        Rule::call_or_access_simple => parse_call_or_access_simple(pair),

        other => err(&pair, format!("unhandled expression rule {:?}", other)),
    }
}

/// Generic lowering for left-associative binary chains: children alternate
/// operand, operator, operand, ...
fn parse_binary_chain(pair: Pair<'_>, op_rules: &[Rule]) -> Result<Expression> {
    let src = pair.clone();
    let children: Vec<_> = pair.into_inner().collect();
    if children.is_empty() {
        return err(&src, "empty expression");
    }

    let mut result = parse_expression(children[0].clone())?;
    let mut i = 1;
    while i + 1 < children.len() || (i < children.len() && op_rules.contains(&children[i].as_rule())) {
        let op_pair = &children[i];
        if !op_rules.contains(&op_pair.as_rule()) {
            return err(op_pair, format!("expected operator, found {:?}", op_pair.as_rule()));
        }
        let right_pair = children.get(i + 1)
            .ok_or_else(|| SemanticError::new("operator without right operand", Some(op_pair.line_col())))?;
        let op = binary_op_from_str(op_pair)?;
        let right = parse_expression(right_pair.clone())?;
        result = Expression::BinaryOp { left: Box::new(result), op, right: Box::new(right) };
        i += 2;
    }
    Ok(result)
}

/// Lowering for `X = { X_simple ~ X_block? }` rules: parse the simple chain,
/// then fold each continuation-block line onto it.
fn parse_binary_with_block(pair: Pair<'_>, block_rule: Rule) -> Result<Expression> {
    let src = pair.clone();
    let mut inner = pair.into_inner();
    let simple = inner.next().ok_or_else(|| SemanticError::new("empty expression", Some(src.line_col())))?;
    let mut result = parse_expression(simple)?;

    if let Some(block) = inner.next() {
        if block.as_rule() != block_rule {
            return err(&block, format!("expected {:?}, found {:?}", block_rule, block.as_rule()));
        }
        for line in block.into_inner() {
            // each line: op ~ X_simple
            let mut line_inner = line.into_inner();
            let op_pair = line_inner.next()
                .ok_or_else(|| SemanticError::new("empty continuation line", None))?;
            let operand_pair = line_inner.next()
                .ok_or_else(|| SemanticError::new("continuation line without operand", Some(op_pair.line_col())))?;
            let op = binary_op_from_str(&op_pair)?;
            let right = parse_expression(operand_pair)?;
            result = Expression::BinaryOp { left: Box::new(result), op, right: Box::new(right) };
        }
    }
    Ok(result)
}

fn binary_op_from_str(pair: &Pair<'_>) -> Result<BinaryOperator> {
    Ok(match pair.as_str().trim() {
        "+" => BinaryOperator::Add,
        "-" => BinaryOperator::Sub,
        "*" => BinaryOperator::Mul,
        "/" => BinaryOperator::Div,
        "%" => BinaryOperator::Mod,
        "**" => BinaryOperator::Pow,
        "==" => BinaryOperator::Eq,
        "!=" => BinaryOperator::Ne,
        "<" => BinaryOperator::Lt,
        "<=" => BinaryOperator::Le,
        ">" => BinaryOperator::Gt,
        ">=" => BinaryOperator::Ge,
        "and" => BinaryOperator::And,
        "or" => BinaryOperator::Or,
        "|" => BinaryOperator::TypeOr,
        "&" => BinaryOperator::TypeAnd,
        "^" => BinaryOperator::BitXor,
        "<<" => BinaryOperator::Shl,
        ">>" => BinaryOperator::Shr,
        ">>>" => BinaryOperator::UShr,
        other => return err(pair, format!("unknown binary operator '{}'", other)),
    })
}

// --- pipelines ---

fn pipeline_op_from_str(pair: &Pair<'_>) -> Result<PipelineOperator> {
    Ok(match pair.as_str() {
        "|>" => PipelineOperator::Pipe,
        "*>" => PipelineOperator::Map,
        "?>" => PipelineOperator::Filter,
        "!>" => PipelineOperator::Handle,
        other => return err(pair, format!("unknown pipeline operator '{}'", other)),
    })
}

/// Flatten the right-nested `pipeline_expr_simple` into (op, expr) links.
/// The first link has op = None.
fn flatten_pipeline_simple(
    pair: Pair<'_>,
    links: &mut Vec<(Option<PipelineOperator>, Expression)>,
) -> Result<()> {
    let mut op = None;
    for p in pair.into_inner() {
        match p.as_rule() {
            Rule::lambda_expr => {
                let expr = parse_expression(p)?;
                links.push((op.take(), expr));
            }
            Rule::pipeline_op => op = Some(pipeline_op_from_str(&p)?),
            Rule::pipeline_expr_simple => {
                // nested tail: its first link carries the pending op
                let mut tail = Vec::new();
                flatten_pipeline_simple(p, &mut tail)?;
                if let Some((first_op, first_expr)) = tail.first().cloned() {
                    debug_assert!(first_op.is_none());
                    links.push((op.take(), first_expr));
                    links.extend(tail.into_iter().skip(1));
                }
            }
            other => return err(&p, format!("unexpected rule {:?} in pipeline", other)),
        }
    }
    Ok(())
}

/// How many lambdas, each the body of the one before, a pipeline chain
/// starts with, written without parentheses: `x => y => ...`.
fn open_lambdas(pair: &Pair<'_>) -> usize {
    let mut p = pair.clone();
    // pipeline_expr -> pipeline_expr_simple -> lambda_expr
    while matches!(p.as_rule(), Rule::pipeline_expr | Rule::pipeline_expr_simple) {
        match p.clone().into_inner().next() {
            Some(first) => p = first,
            None => return 0,
        }
    }
    let mut n = 0;
    while p.as_rule() == Rule::lambda_expr {
        let children: Vec<Pair<'_>> = p.clone().into_inner().collect();
        if !children.iter().any(|c| c.as_rule() == Rule::lambda_op) {
            break;
        }
        n += 1;
        match children.last() {
            Some(body) => p = body.clone(),
            None => break,
        }
    }
    n
}

/// A chain that starts with a lambda written without parentheses belongs
/// to the lambda's body: `x => x |> f` is `x => (x |> f)`, and a match arm
/// `n => n |> f` pipes inside the arm. (A lambda as a pipeline stage,
/// `xs ?> x => x > 1 |> sum`, is not the head and still ends at the next
/// operator.)
fn build_pipeline_in_lambda(links: Vec<(Option<PipelineOperator>, Expression)>, open: usize) -> Result<Expression> {
    if open == 0 || links.len() < 2 {
        return build_pipeline(links);
    }
    let mut iter = links.into_iter();
    let (_, head) = iter.next().unwrap();
    match head {
        Expression::Lambda { params, body } => {
            let mut inner = vec![(None, *body)];
            inner.extend(iter);
            let body = build_pipeline_in_lambda(inner, open - 1)?;
            Ok(Expression::Lambda { params, body: Box::new(body) })
        }
        head => {
            let mut all = vec![(None, head)];
            all.extend(iter);
            build_pipeline(all)
        }
    }
}

fn build_pipeline(links: Vec<(Option<PipelineOperator>, Expression)>) -> Result<Expression> {
    let mut iter = links.into_iter();
    let (_, mut result) = match iter.next() {
        Some(first) => first,
        None => return Err(SemanticError::new("empty pipeline", None)),
    };
    for (op, expr) in iter {
        let op = op.ok_or_else(|| SemanticError::new("pipeline link without operator", None))?;
        result = Expression::Pipeline { left: Box::new(result), op, right: Box::new(expr) };
    }
    Ok(result)
}

fn parse_pipeline(pair: Pair<'_>) -> Result<Expression> {
    let open = open_lambdas(&pair);
    let mut links = Vec::new();
    for p in pair.into_inner() {
        match p.as_rule() {
            Rule::pipeline_expr_simple => flatten_pipeline_simple(p, &mut links)?,
            Rule::pipeline_block => {
                for line in p.into_inner() {
                    // pipeline_block_line: pipeline_op ~ pipeline_expr_simple
                    let mut op = None;
                    for lp in line.into_inner() {
                        match lp.as_rule() {
                            Rule::pipeline_op => op = Some(pipeline_op_from_str(&lp)?),
                            Rule::pipeline_expr_simple => {
                                let mut tail = Vec::new();
                                flatten_pipeline_simple(lp, &mut tail)?;
                                if let Some((first_op, first_expr)) = tail.first().cloned() {
                                    debug_assert!(first_op.is_none());
                                    links.push((op.take(), first_expr));
                                    links.extend(tail.into_iter().skip(1));
                                }
                            }
                            Rule::comment => {}
                            other => return err(&lp, format!("unexpected rule {:?} in pipeline line", other)),
                        }
                    }
                }
            }
            other => return err(&p, format!("unexpected rule {:?} in pipeline", other)),
        }
    }
    build_pipeline_in_lambda(links, open)
}

// --- lambdas ---

fn parse_lambda_expression(pair: Pair<'_>) -> Result<Expression> {
    let mut children = pair.into_inner();
    let prefix = match children.next() {
        Some(p) => p,
        None => return Err(SemanticError::new("empty lambda expression", None)),
    };

    // No `=>` follows: the prefix is just an ordinary expression.
    let Some(second) = children.next() else {
        return parse_expression(prefix);
    };

    // prefix ~ '=>' ~ body: the prefix expression becomes the parameter list.
    let params = params_from_prefix(&prefix)?;
    let mut body: Option<Expression> = None;
    let mut body_stmts: Vec<Stmt> = Vec::new();
    for p in std::iter::once(second).chain(children) {
        match p.as_rule() {
            Rule::lambda_op => {}
            Rule::lambda_expr => body = Some(parse_lambda_expression(p)?),
            Rule::statement => body_stmts.push(parse_statement(p)?),
            Rule::return_stmt | Rule::break_stmt | Rule::continue_stmt => body_stmts.push(parse_control(p)?),
            other => return err(&p, format!("unexpected rule {:?} in lambda", other)),
        }
    }

    let body = match (body, body_stmts.is_empty()) {
        (Some(b), _) => b,
        (None, false) => Expression::Block(body_stmts),
        (None, true) => return Err(SemanticError::new("lambda without body", None)),
    };

    Ok(Expression::Lambda { params, body: Box::new(body) })
}

/// The expression before `=>`, parsed once as a general prefix, becomes the
/// parameter list: `x`, `x: int`, `()`, `(a, b = 1)`, `{age}`, `[a, b]`, `0`.
fn params_from_prefix(prefix: &Pair<'_>) -> Result<Vec<Param>> {
    // Walk down the single-child precedence chain to the typecheck level,
    // where parenthesized parameter lists and plain patterns live.
    let mut p = prefix.clone();
    while p.as_rule() != Rule::typecheck {
        let mut inner = p.clone().into_inner();
        match (inner.next(), inner.next()) {
            (Some(only), None) => p = only,
            _ => break, // multi-child level (e.g. `a = 1`, `-1`): handled below
        }
    }
    if p.as_rule() == Rule::typecheck {
        return params_from_typecheck_pair(p);
    }

    let expr = parse_expression(prefix.clone())?;
    // `name = default` lowers to assignment sugar; unwrap it.
    if let Expression::Block(ref stmts) = expr
        && let [Stmt { node: Statement::Assignment { targets, value }, .. }] = stmts.as_slice()
            && let [(pattern, AssignmentOp::Assign)] = targets.as_slice() {
                return Ok(vec![Param {
                    is_public: false,
                    is_var: false,
                    pattern: pattern.clone(),
                    default: Some(value.clone()),
                }]);
            }
    let pattern = expression_to_pattern(expr, prefix)?;
    Ok(vec![Param { is_public: false, is_var: false, pattern, default: None }])
}

/// A single-token lambda parameter comes in as a `typecheck` pair. It may be:
/// - a plain pattern: `x`, `x: int`, `{age}`, `[a, b]`, `0`, `"{h}:{m}"`
/// - a parenthesized parameter list that the grammar parsed as an atom:
///   `()`, `(x)`, `(a, b = 1)`
fn params_from_typecheck_pair(pair: Pair<'_>) -> Result<Vec<Param>> {
    // Check for the parenthesized case: typecheck -> call_or_access ->
    // call_or_access_simple -> paren_expr (with no postfix operations).
    let mut probe = pair.clone().into_inner();
    if let (Some(call_or_access), None) = (probe.next(), probe.next()) {
        let mut inner = call_or_access.clone().into_inner();
        if let (Some(simple), None) = (inner.next(), inner.next())
            && simple.as_rule() == Rule::call_or_access_simple {
                let parts: Vec<_> = simple.into_inner().collect();
                if parts.len() == 1 && parts[0].as_rule() == Rule::paren_expr {
                    return parts[0].clone().into_inner()
                        .map(|elem| param_from_paren_element(elem))
                        .collect();
                }
            }
    }

    let expr = parse_expression(pair.clone())?;
    let pattern = expression_to_pattern(expr, &pair)?;
    Ok(vec![Param { is_public: false, is_var: false, pattern, default: None }])
}

/// One comma-separated element of a parenthesized parameter list. The grammar
/// parses it as a full expression; parameters live at the assignment level
/// (`pattern` or `pattern = default`), so descend the single-child chain.
fn param_from_paren_element(pair: Pair<'_>) -> Result<Param> {
    let mut p = pair.clone();
    while p.as_rule() != Rule::assignment_expr {
        let mut inner = p.clone().into_inner();
        match (inner.next(), inner.next()) {
            (Some(only), None) => p = only,
            _ => return err(&pair, "invalid parameter"),
        }
    }
    parse_param_from_assignment_expr(p)
}

// --- loop / if expressions ---

fn parse_loop_expression(pair: Pair<'_>) -> Result<Expression> {
    let children: Vec<_> = pair.into_inner().collect();

    // Alternative: plain expression_small (assignment_expr) or if_expr only
    if children.len() == 1 {
        return parse_expression(children[0].clone());
    }

    let mut clauses: Vec<CompClause> = Vec::new();
    let mut body: Option<Expression> = None;
    let mut body_stmts: Vec<Stmt> = Vec::new();
    let mut iter = children.into_iter().peekable();

    while let Some(p) = iter.peek().cloned() {
        match p.as_rule() {
            Rule::kw_for => {
                iter.next();
                let (pattern, iterables) = parse_for_header(&mut iter)?;
                clauses.push(CompClause::For { pattern, iterables });
            }
            Rule::kw_do => {
                iter.next();
            }
            Rule::if_expr => {
                iter.next();
                body = Some(parse_if_expression(p)?);
            }
            Rule::assignment_expr | Rule::pipeline_expr_simple => {
                iter.next();
                body = Some(parse_expression(p)?);
            }
            Rule::statement => {
                iter.next();
                body_stmts.push(parse_statement(p)?);
            }
            other => return err(&p, format!("unexpected rule {:?} in loop expression", other)),
        }
    }

    let body = match (body, body_stmts.is_empty()) {
        (Some(b), _) => b,
        (None, false) => Expression::Block(body_stmts),
        (None, true) => return Err(SemanticError::new("loop expression without body", None)),
    };

    if clauses.is_empty() {
        return Ok(body);
    }
    Ok(Expression::Comprehension { clauses, body: Box::new(body) })
}

fn parse_if_expression(pair: Pair<'_>) -> Result<Expression> {
    let children: Vec<_> = pair.into_inner().collect();

    let mut condition: Option<Expression> = None;
    let mut then_branch: Option<Expression> = None;
    let mut then_stmts: Vec<Stmt> = Vec::new();
    let mut elif_branches: Vec<(Expression, Expression)> = Vec::new();
    let mut else_branch: Option<Expression> = None;

    enum Mode { Cond, Then, ElifCond, ElifThen, Else }
    let mut mode = Mode::Cond;
    let mut pending_elif_cond: Option<Expression> = None;

    for p in children {
        match p.as_rule() {
            Rule::kw_if => {}
            Rule::kw_do => {
                mode = match mode {
                    Mode::Cond => Mode::Then,
                    Mode::ElifCond => Mode::ElifThen,
                    m => m,
                };
            }
            Rule::kw_elif => mode = Mode::ElifCond,
            Rule::kw_else => mode = Mode::Else,
            Rule::assignment_expr | Rule::pipeline_expr_simple => {
                let expr = parse_expression(p)?;
                match mode {
                    Mode::Cond => condition = Some(expr),
                    Mode::Then => then_branch = Some(expr),
                    Mode::ElifCond => pending_elif_cond = Some(expr),
                    Mode::ElifThen => {
                        let cond = pending_elif_cond.take()
                            .ok_or_else(|| SemanticError::new("elif branch without condition", None))?;
                        elif_branches.push((cond, expr));
                    }
                    Mode::Else => else_branch = Some(expr),
                }
            }
            Rule::statement => then_stmts.push(parse_statement(p)?),
            other => return err(&p, format!("unexpected rule {:?} in if expression", other)),
        }
    }

    let condition = condition.ok_or_else(|| SemanticError::new("if expression without condition", None))?;
    let then_branch = match (then_branch, then_stmts.is_empty()) {
        (Some(b), _) => b,
        (None, false) => Expression::Block(then_stmts),
        (None, true) => return Err(SemanticError::new("if expression without body", None)),
    };

    Ok(Expression::IfExpr {
        condition: Box::new(condition),
        then_branch: Box::new(then_branch),
        elif_branches,
        else_branch: else_branch.map(Box::new),
    })
}

// --- ranges, typecheck ---

fn parse_range_expression(pair: Pair<'_>) -> Result<Expression> {
    let mut start = None;
    let mut end = None;
    let mut found_op = false;

    for p in pair.into_inner() {
        match p.as_rule() {
            Rule::range_op => found_op = true,
            _ => {
                let expr = parse_expression(p)?;
                if !found_op {
                    start = Some(Box::new(expr));
                } else {
                    end = Some(Box::new(expr));
                }
            }
        }
    }

    if !found_op {
        return start.map(|b| *b).ok_or_else(|| SemanticError::new("empty range expression", None));
    }
    Ok(Expression::Range { start, end })
}

fn parse_typecheck_expression(pair: Pair<'_>) -> Result<Expression> {
    let src = pair.clone();
    let mut inner = pair.into_inner();
    let left_pair = inner.next()
        .ok_or_else(|| SemanticError::new("empty typecheck", Some(src.line_col())))?;
    let left = parse_expression(left_pair)?;

    match inner.next() {
        None => Ok(left),
        Some(op) if op.as_rule() == Rule::typecheck_op => {
            let type_pair = inner.next()
                .ok_or_else(|| SemanticError::new("type check without type", Some(op.line_col())))?;
            let type_expr = parse_expression(type_pair)?;
            if matches!(left, Expression::Call { .. }) {
                return err(&src, "a function call cannot be the target of a type check");
            }
            Ok(Expression::TypeCheck { expression: Box::new(left), type_expr: Box::new(type_expr) })
        }
        Some(other) => err(&other, format!("unexpected rule {:?} in typecheck", other.as_rule())),
    }
}

// --- calls, member access ---

fn parse_call_or_access_simple(pair: Pair<'_>) -> Result<Expression> {
    let mut inner = pair.into_inner();
    let base = inner.next().ok_or_else(|| SemanticError::new("empty call_or_access", None))?;
    let mut expr = parse_expression(base)?;
    expr = apply_postfix_parts(expr, &mut inner)?;
    Ok(expr)
}

/// Apply a sequence of postfix parts (member access ops + atoms, call args,
/// index args) to a base expression.
fn apply_postfix_parts<'a>(
    mut expr: Expression,
    parts: &mut impl Iterator<Item = Pair<'a>>,
) -> Result<Expression> {
    while let Some(part) = parts.next() {
        match part.as_rule() {
            Rule::member_access_op => {
                let member_pair = parts.next()
                    .ok_or_else(|| SemanticError::new("member access without member", Some(part.line_col())))?;
                match member_pair.as_rule() {
                    Rule::identifier => {
                        expr = Expression::MemberAccess {
                            object: Box::new(expr),
                            member: member_pair.as_str().to_string(),
                        };
                    }
                    Rule::object => {
                        // `expr.{...}` — spread target
                        let entries = parse_object_literal(member_pair.clone())?;
                        match entries {
                            Expression::Object(items)
                                if items.len() == 1 && items[0] == ObjectEntry::Spread =>
                            {
                                expr = Expression::SpreadMember { object: Box::new(expr) };
                            }
                            _ => {
                                return err(&member_pair,
                                    "only `.{...}` is supported for object spread access");
                            }
                        }
                    }
                    other => {
                        return err(&member_pair,
                            format!("invalid member access: expected a name, found {:?}", other));
                    }
                }
            }
            Rule::function_call_args => {
                let (args, named_args) = parse_call_args(part)?;
                expr = Expression::Call { function: Box::new(expr), args, named_args };
            }
            Rule::list_access_args => {
                let src = part.clone();
                let (mut indices, named) = parse_call_args(part)?;
                if !named.is_empty() {
                    return err(&src, "indexing does not take keyword arguments");
                }
                if indices.len() != 1 {
                    return err(&src, format!("indexing takes exactly one argument, found {}", indices.len()));
                }
                expr = Expression::Index {
                    object: Box::new(expr),
                    index: Box::new(indices.remove(0)),
                };
            }
            other => return err(&part, format!("unexpected postfix rule {:?}", other)),
        }
    }
    Ok(expr)
}

type CallArgs = (Vec<Expression>, Vec<(String, Expression)>);

fn parse_call_args(pair: Pair<'_>) -> Result<CallArgs> {
    let mut args = Vec::new();
    let mut named: Vec<(String, Expression)> = Vec::new();
    for p in pair.into_inner() {
        match p.as_rule() {
            Rule::named_arg => {
                let src = p.clone();
                let mut inner = p.into_inner();
                let name = inner.next()
                    .ok_or_else(|| SemanticError::new("malformed keyword argument", None))?
                    .as_str().to_string();
                let value_pair = inner.next()
                    .ok_or_else(|| SemanticError::new("malformed keyword argument", None))?;
                if named.iter().any(|(n, _)| *n == name) {
                    return err(&src, format!("keyword argument '{}' given twice", name));
                }
                named.push((name, parse_expression(value_pair)?));
            }
            Rule::pipeline_expr => {
                let src = p.clone();
                if !named.is_empty() {
                    return err(&src, "positional arguments must come before keyword arguments");
                }
                args.push(parse_expression(p)?);
            }
            _ => {}
        }
    }
    Ok((args, named))
}

/// Apply an `access_block` (multi-line `.method()` continuation) to a base expression.
fn apply_access_block(mut expr: Expression, block: Pair<'_>) -> Result<Expression> {
    for line in block.into_inner() {
        // access_block_line: member_access_op ~ call_or_access_simple
        let mut inner = line.into_inner();
        let op = inner.next()
            .ok_or_else(|| SemanticError::new("empty access line", None))?;

        let chain = inner.next()
            .ok_or_else(|| SemanticError::new("access line without member", Some(op.line_col())))?;

        // The chain's first atom is the member name; the rest are postfix parts.
        let mut chain_inner = chain.clone().into_inner();
        let first = chain_inner.next()
            .ok_or_else(|| SemanticError::new("empty access chain", Some(chain.line_col())))?;
        if first.as_rule() != Rule::identifier {
            return err(&first, "a `.member` continuation line must start with a member name");
        }
        expr = Expression::MemberAccess {
            object: Box::new(expr),
            member: first.as_str().to_string(),
        };
        expr = apply_postfix_parts(expr, &mut chain_inner)?;
    }
    Ok(expr)
}

// --- literals ---

fn parse_number_literal(pair: Pair<'_>) -> Result<Expression> {
    let inner = pair.clone().into_inner().next()
        .ok_or_else(|| SemanticError::new("empty number", Some(pair.line_col())))?;
    let text = inner.as_str().to_string();
    let lit = match inner.as_rule() {
        Rule::decimal_number => NumberLiteral::Decimal(text),
        Rule::hex_number => NumberLiteral::Hex(text),
        Rule::bin_number => NumberLiteral::Binary(text),
        Rule::scientific_number => NumberLiteral::Scientific(text),
        other => return err(&inner, format!("unknown number form {:?}", other)),
    };
    Ok(Expression::Number(lit))
}

fn parse_fstring_parts(pair: Pair<'_>) -> Result<Vec<FStringPart>> {
    let mut parts: Vec<FStringPart> = Vec::new();

    fn push_text(parts: &mut Vec<FStringPart>, text: &str) {
        if let Some(FStringPart::Text(existing)) = parts.last_mut() {
            existing.push_str(text);
        } else {
            parts.push(FStringPart::Text(text.to_string()));
        }
    }

    for p in pair.into_inner() {
        match p.as_rule() {
            Rule::fstring_text => push_text(&mut parts, p.as_str()),
            Rule::fstring_escape => {
                let decoded = decode_escape(p.as_str())
                    .ok_or_else(|| SemanticError::new(
                        format!("invalid escape sequence '{}'", p.as_str()),
                        Some(p.line_col())))?;
                push_text(&mut parts, &decoded);
            }
            Rule::fstring_interp => {
                let inner = p.clone().into_inner().next()
                    .ok_or_else(|| SemanticError::new("empty interpolation", Some(p.line_col())))?;
                match inner.as_rule() {
                    Rule::fstring_formatted => {
                        let mut fmt_inner = inner.into_inner();
                        let expr_pair = fmt_inner.next()
                            .ok_or_else(|| SemanticError::new("empty interpolation", Some(p.line_col())))?;
                        let spec = fmt_inner.next()
                            .map(|s| s.as_str().trim_start_matches(':').to_string());
                        parts.push(FStringPart::Expression(parse_expression(expr_pair)?, spec));
                    }
                    Rule::fstring_split => {
                        let mut split = inner.into_inner();
                        let (Some(target), Some(spec)) = (split.next(), split.next()) else {
                            return err(&p, "malformed interpolation");
                        };
                        let text = target.as_str();
                        let parsed = <crate::FireParser as pest::Parser<Rule>>::parse(Rule::fstring_expression, text)
                            .map_err(|_| SemanticError::new(format!("cannot read `{}` before the format spec `{}` as an expression", text.trim(), spec.as_str()), Some(target.line_col())))?;
                        let expr = parsed.into_iter().next().and_then(|e| e.into_inner().find(|x| x.as_rule() == Rule::pipeline_expr));
                        let Some(expr) = expr else {
                            return err(&target, "empty interpolation");
                        };
                        let spec = spec.as_str().trim_start_matches(':').to_string();
                        parts.push(FStringPart::Expression(parse_expression(expr)?, Some(spec)));
                    }
                    _ => parts.push(FStringPart::Expression(parse_expression(inner)?, None)),
                }
            }
            other => return err(&p, format!("unexpected rule {:?} in f-string", other)),
        }
    }
    Ok(parts)
}

fn decode_escape(escape: &str) -> Option<String> {
    let rest = escape.strip_prefix('\\')?;
    let mut chars = rest.chars();
    let c = chars.next()?;
    let decoded = match c {
        '\\' => '\\',
        '"' => '"',
        '{' => '{',
        '}' => '}',
        'r' => '\r',
        'n' => '\n',
        't' => '\t',
        'b' => '\u{0008}',
        'f' => '\u{000C}',
        'v' => '\u{000B}',
        '0' => '\0',
        'x' | 'u' | 'U' => {
            let hex: String = chars.collect();
            let code = u32::from_str_radix(&hex, 16).ok()?;
            return char::from_u32(code).map(|c| c.to_string());
        }
        _ => return None,
    };
    Some(decoded.to_string())
}

fn parse_list_literal(pair: Pair<'_>) -> Result<Expression> {
    let mut entries = Vec::new();
    for p in pair.into_inner() {
        if p.as_rule() == Rule::list_entry {
            let inner = p.clone().into_inner().next()
                .ok_or_else(|| SemanticError::new("empty list entry", Some(p.line_col())))?;
            entries.push(parse_expression(inner)?);
        }
    }
    Ok(Expression::List(entries))
}

fn parse_object_literal(pair: Pair<'_>) -> Result<Expression> {
    let mut entries = Vec::new();
    for p in pair.into_inner() {
        if p.as_rule() != Rule::object_entry {
            continue;
        }
        let children: Vec<_> = p.clone().into_inner().collect();
        match children.as_slice() {
            [single] if single.as_rule() == Rule::identifier => {
                entries.push(ObjectEntry::Shorthand(single.as_str().to_string()));
            }
            [single] if single.as_rule() == Rule::ellipsis => {
                entries.push(ObjectEntry::Spread);
            }
            [key, value] if key.as_rule() == Rule::identifier => {
                entries.push(ObjectEntry::KeyValue {
                    key: key.as_str().to_string(),
                    value: parse_expression(value.clone())?,
                });
            }
            _ => return err(&p, "invalid object entry"),
        }
    }
    Ok(Expression::Object(entries))
}

// ---------------------------------------------------------------------------
// Expression -> Pattern conversion
// ---------------------------------------------------------------------------

/// Operator symbols that objects may define via `` `+` = (other) => ... ``.
pub const OPERATOR_SYMBOLS: &[&str] = &["+", "-", "*", "/", "%", "**"];

pub fn expression_to_pattern(expr: Expression, src: &Pair<'_>) -> Result<Pattern> {
    match expr {
        Expression::Identifier(name) => Ok(Pattern::Identifier(name)),
        // `` `+` `` as a binding target declares a custom operator
        Expression::TString(s) if OPERATOR_SYMBOLS.contains(&s.as_str()) => {
            Ok(Pattern::Identifier(s))
        }
        Expression::TypeCheck { expression, type_expr } => {
            let inner = expression_to_pattern(*expression, src)?;
            Ok(Pattern::Typed { pattern: Box::new(inner), type_expr: *type_expr })
        }
        Expression::Number(_) | Expression::Str(_) | Expression::TString(_)
        | Expression::Boolean(_) | Expression::Nothing => Ok(Pattern::Literal(expr)),
        Expression::UnaryOp { op: UnaryOperator::Minus, ref operand }
            if matches!(**operand, Expression::Number(_)) => Ok(Pattern::Literal(expr)),
        Expression::FString(parts) => {
            if parts.iter().any(|p| matches!(p, FStringPart::Expression(..))) {
                // every interpolated expression must itself be a bindable pattern
                let mut checked = Vec::new();
                for part in parts {
                    match part {
                        FStringPart::Text(t) => checked.push(FStringPart::Text(t)),
                        // format specs are ignored in pattern (reverse) mode
                        FStringPart::Expression(e, spec) => {
                            match &e {
                                Expression::Identifier(_) => checked.push(FStringPart::Expression(e, spec)),
                                _ => return err(src, "only plain names can be captured in an f-string pattern"),
                            }
                        }
                    }
                }
                Ok(Pattern::FString(checked))
            } else {
                // no interpolation: a literal string pattern
                let text = parts.iter().map(|p| match p {
                    FStringPart::Text(t) => t.as_str(),
                    FStringPart::Expression(..) => unreachable!(),
                }).collect::<String>();
                Ok(Pattern::Literal(Expression::Str(text)))
            }
        }
        Expression::List(entries) => {
            let mut patterns = Vec::new();
            for e in entries {
                patterns.push(match e {
                    Expression::UnaryOp { op: UnaryOperator::Spread, operand } => {
                        match *operand {
                            Expression::Identifier(name) => Pattern::Rest(Some(name)),
                            _ => return err(src, "a rest pattern must be `...name` or `...`"),
                        }
                    }
                    Expression::Ellipsis => Pattern::Rest(None),
                    other => expression_to_pattern(other, src)?,
                });
            }
            let rest_count = patterns.iter().filter(|p| matches!(p, Pattern::Rest(_))).count();
            if rest_count > 1 {
                return err(src, "a list pattern may contain at most one rest pattern");
            }
            Ok(Pattern::List(patterns))
        }
        Expression::Object(entries) => {
            let mut pairs = Vec::new();
            for e in entries {
                match e {
                    ObjectEntry::Shorthand(name) => {
                        pairs.push((name.clone(), Pattern::Identifier(name)));
                    }
                    ObjectEntry::KeyValue { key, value } => {
                        pairs.push((key, expression_to_pattern(value, src)?));
                    }
                    ObjectEntry::Spread => {
                        return err(src, "`...` is not needed in object patterns (extra keys always match)");
                    }
                }
            }
            Ok(Pattern::Object(pairs))
        }
        Expression::MemberAccess { object, member } => Ok(Pattern::Member { object: *object, member }),
        // `Node(l, v, r)`: a constructor pattern
        Expression::Call { function, args, named_args } => {
            let name = match *function {
                Expression::Identifier(n) => n,
                _ => return err(src, "only a constructor can be called in a pattern"),
            };
            if !named_args.is_empty() {
                return err(src, "constructor patterns take positional sub-patterns only");
            }
            let mut subs = Vec::new();
            for a in args {
                subs.push(expression_to_pattern(a, src)?);
            }
            Ok(Pattern::Ctor(name, subs))
        }
        Expression::Index { object, index } => {
            Ok(Pattern::Index { object: *object, index: *index })
        }
        Expression::SpreadMember { object } => Ok(Pattern::SpreadInto { object: *object }),
        other => err(src, format!("invalid assignment target / pattern: {}", other)),
    }
}

// ---------------------------------------------------------------------------
// Pretty printing
// ---------------------------------------------------------------------------

impl fmt::Display for Program {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for (i, stmt) in self.statements.iter().enumerate() {
            if i > 0 {
                writeln!(f)?;
            }
            write!(f, "{}", stmt.node.to_string_with_indent(0))?;
        }
        Ok(())
    }
}

impl fmt::Display for Stmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.node.to_string_with_indent(0))
    }
}

impl fmt::Display for Statement {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.to_string_with_indent(0))
    }
}

fn write_body(out: &mut String, body: &[Stmt], indent_level: usize) {
    for stmt in body {
        out.push_str(&stmt.node.to_string_with_indent(indent_level));
        out.push('\n');
    }
}

impl Statement {
    fn to_string_with_indent(&self, level: usize) -> String {
        let indent = "    ".repeat(level);
        match self {
            Statement::Documentation(content) => format!("{}## {}", indent, content),
            Statement::Comment(content) => format!("{}# {}", indent, content),
            Statement::Declaration { is_public, is_mutable, pattern, value } => {
                let mut out = indent.clone();
                if *is_public { out.push_str("public "); }
                if *is_mutable { out.push_str("var "); }
                out.push_str(&format!("{} = {}", pattern, value.to_string_with_indent(level)));
                out
            }
            Statement::Assignment { targets, value } => {
                let mut out = indent.clone();
                for (target, op) in targets {
                    out.push_str(&format!("{} {} ", target, op));
                }
                out.push_str(&value.to_string_with_indent(level));
                out
            }
            Statement::Return(Some(expr)) => format!("{}return {}", indent, expr.to_string_with_indent(level)),
            Statement::Return(None) => format!("{}return", indent),
            Statement::Break => format!("{}break", indent),
            Statement::Continue => format!("{}continue", indent),
            Statement::While { condition, body } => {
                let mut out = format!("{}while {}\n", indent, condition);
                write_body(&mut out, body, level + 1);
                out.trim_end().to_string()
            }
            Statement::For { pattern, iterables, body } => {
                let iters = iterables.iter().map(|e| e.to_string())
                    .collect::<Vec<_>>().join(", ");
                let mut out = format!("{}for {} in {}\n", indent, pattern, iters);
                write_body(&mut out, body, level + 1);
                out.trim_end().to_string()
            }
            Statement::If { condition, body, elif_branches, else_body } => {
                let mut out = format!("{}if {}\n", indent, condition);
                write_body(&mut out, body, level + 1);
                for (cond, stmts) in elif_branches {
                    out.push_str(&format!("{}elif {}\n", indent, cond));
                    write_body(&mut out, stmts, level + 1);
                }
                if let Some(else_stmts) = else_body {
                    out.push_str(&format!("{}else\n", indent));
                    write_body(&mut out, else_stmts, level + 1);
                }
                out.trim_end().to_string()
            }
            Statement::Match { subject, arms } => {
                let mut out = format!("{}match {}\n", indent, subject);
                let arm_indent = "    ".repeat(level + 1);
                for arm in arms {
                    let guard = match &arm.guard {
                        Some(cond) => format!(" if {}", cond),
                        None => String::new(),
                    };
                    out.push_str(&format!("{}{}{} => {}\n", arm_indent, arm.pattern, guard,
                        arm.body.to_string_with_indent(level + 1)));
                }
                out.trim_end().to_string()
            }
            Statement::TypeDecl { name, ctors } => {
                let mut out = format!("{}type {}\n", indent, name);
                for c in ctors {
                    out.push_str(&format!("{}    {}", indent, c.name));
                    if !c.fields.is_empty() {
                        let fs: Vec<String> = c.fields.iter().map(|(n, t)| match t {
                            Some(t) => format!("{}: {}", n, t),
                            None => n.clone(),
                        }).collect();
                        out.push_str(&format!("({})", fs.join(", ")));
                    }
                    out.push('\n');
                }
                out.trim_end().to_string()
            }
            Statement::Law { name, vars, hyp, claim } => {
                let mut out = format!("{}law {}\n", indent, name);
                if !vars.is_empty() {
                    let vs: Vec<String> = vars.iter().map(|(n, t)| format!("{}: {}", n, t)).collect();
                    out.push_str(&format!("{}    for {}", indent, vs.join(", ")));
                    if let Some(h) = hyp {
                        out.push_str(&format!(" if {}", h));
                    }
                    out.push('\n');
                }
                out.push_str(&format!("{}    {}", indent, claim));
                out
            }
            Statement::Def { is_public, is_unsafe, name, params, return_type, body } => {
                let mut out = indent.clone();
                if *is_public { out.push_str("public "); }
                if *is_unsafe { out.push_str("unsafe "); }
                out.push_str(&format!("def {}(", name));
                for (i, param) in params.iter().enumerate() {
                    if i > 0 { out.push_str(", "); }
                    out.push_str(&param.to_string());
                }
                out.push(')');
                if let Some(ret) = return_type {
                    out.push_str(&format!(": {}", ret));
                }
                out.push('\n');
                write_body(&mut out, body, level + 1);
                out.trim_end().to_string()
            }
            Statement::Expression(expr) => format!("{}{}", indent, expr.to_string_with_indent(level)),
        }
    }
}

impl fmt::Display for Param {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.is_public {
            write!(f, "public ")?;
        }
        write!(f, "{}", self.pattern)?;
        if let Some(default) = &self.default {
            write!(f, " = {}", default)?;
        }
        Ok(())
    }
}

impl fmt::Display for Pattern {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Pattern::Identifier(name) => write!(f, "{}", name),
            Pattern::Typed { pattern, type_expr } => write!(f, "{}: {}", pattern, type_expr),
            Pattern::Literal(expr) => write!(f, "{}", expr),
            Pattern::List(items) => {
                write!(f, "[")?;
                for (i, item) in items.iter().enumerate() {
                    if i > 0 { write!(f, ", ")?; }
                    write!(f, "{}", item)?;
                }
                write!(f, "]")
            }
            Pattern::Rest(Some(name)) => write!(f, "...{}", name),
            Pattern::Rest(None) => write!(f, "..."),
            Pattern::Object(entries) => {
                write!(f, "{{")?;
                for (i, (key, pattern)) in entries.iter().enumerate() {
                    if i > 0 { write!(f, ", ")?; }
                    match pattern {
                        Pattern::Identifier(name) if name == key => write!(f, "{}", key)?,
                        _ => write!(f, "{}: {}", key, pattern)?,
                    }
                }
                write!(f, "}}")
            }
            Pattern::FString(parts) => {
                write!(f, "\"")?;
                for part in parts {
                    write!(f, "{}", part)?;
                }
                write!(f, "\"")
            }
            Pattern::Ctor(name, subs) => {
                write!(f, "{}(", name)?;
                for (i, item) in subs.iter().enumerate() {
                    if i > 0 { write!(f, ", ")?; }
                    write!(f, "{}", item)?;
                }
                write!(f, ")")
            }
            Pattern::Member { object, member } => write!(f, "{}.{}", object, member),
            Pattern::Index { object, index } => write!(f, "{}[{}]", object, index),
            Pattern::SpreadInto { object } => write!(f, "{}.{{...}}", object),
        }
    }
}

impl fmt::Display for AssignmentOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = match self {
            AssignmentOp::Assign => "=",
            AssignmentOp::AddAssign => "+=",
            AssignmentOp::SubAssign => "-=",
            AssignmentOp::MulAssign => "*=",
            AssignmentOp::DivAssign => "/=",
            AssignmentOp::ModAssign => "%=",
            AssignmentOp::PowAssign => "**=",
            AssignmentOp::BitAndAssign => "&=",
            AssignmentOp::BitOrAssign => "|=",
            AssignmentOp::BitXorAssign => "^=",
            AssignmentOp::ShlAssign => "<<=",
            AssignmentOp::ShrAssign => ">>=",
            AssignmentOp::UShrAssign => ">>>=",
        };
        write!(f, "{}", s)
    }
}

impl Expression {
    fn to_string_with_indent(&self, level: usize) -> String {
        match self {
            Expression::Block(stmts) => {
                let mut out = String::new();
                for stmt in stmts {
                    out.push('\n');
                    out.push_str(&stmt.node.to_string_with_indent(level + 1));
                }
                out
            }
            Expression::Lambda { params, body } => {
                let params_str = format_lambda_params(params);
                format!("{} => {}", params_str, body.to_string_with_indent(level))
            }
            Expression::IfExpr { condition, then_branch, elif_branches, else_branch } => {
                let mut out = format!("if {} do {}", condition, then_branch.to_string_with_indent(level));
                for (cond, branch) in elif_branches {
                    out.push_str(&format!(" elif {} do {}", cond, branch.to_string_with_indent(level)));
                }
                if let Some(e) = else_branch {
                    out.push_str(&format!(" else {}", e.to_string_with_indent(level)));
                }
                out
            }
            _ => format!("{}", self),
        }
    }
}

fn format_lambda_params(params: &[Param]) -> String {
    if params.len() == 1 && params[0].default.is_none() && !params[0].is_public {
        format!("{}", params[0].pattern)
    } else {
        let inner = params.iter().map(|p| p.to_string()).collect::<Vec<_>>().join(", ");
        format!("({})", inner)
    }
}

impl fmt::Display for Expression {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Expression::Identifier(name) => write!(f, "{}", name),
            Expression::Import(module) => write!(f, "${}", module),
            Expression::Number(lit) => write!(f, "{}", lit),
            Expression::Str(content) => write!(f, "'{}'", content),
            Expression::FString(parts) => {
                write!(f, "\"")?;
                for part in parts {
                    write!(f, "{}", part)?;
                }
                write!(f, "\"")
            }
            Expression::TString(content) => write!(f, "`{}`", content),
            Expression::Boolean(value) => write!(f, "{}", value),
            Expression::Nothing => write!(f, "nothing"),
            Expression::Ellipsis => write!(f, "..."),
            Expression::PreviousResult => write!(f, "$"),
            Expression::List(entries) => {
                write!(f, "[")?;
                for (i, entry) in entries.iter().enumerate() {
                    if i > 0 { write!(f, ", ")?; }
                    write!(f, "{}", entry)?;
                }
                write!(f, "]")
            }
            Expression::Object(entries) => {
                write!(f, "{{")?;
                for (i, entry) in entries.iter().enumerate() {
                    if i > 0 { write!(f, ", ")?; }
                    write!(f, "{}", entry)?;
                }
                write!(f, "}}")
            }
            Expression::BinaryOp { left, op, right } => write!(f, "({} {} {})", left, op, right),
            Expression::UnaryOp { op, operand } => match op {
                UnaryOperator::Plus => write!(f, "+{}", operand),
                UnaryOperator::Minus => write!(f, "-{}", operand),
                UnaryOperator::Not => write!(f, "not {}", operand),
                UnaryOperator::Spread => write!(f, "...{}", operand),
            },
            Expression::Lambda { params, body } => {
                write!(f, "{} => {}", format_lambda_params(params), body)
            }
            Expression::Block(stmts) => {
                write!(f, "(block:")?;
                for stmt in stmts {
                    write!(f, " {};", stmt.node)?;
                }
                write!(f, ")")
            }
            Expression::Call { function, args, named_args } => {
                write!(f, "{}(", function)?;
                for (i, arg) in args.iter().enumerate() {
                    if i > 0 { write!(f, ", ")?; }
                    write!(f, "{}", arg)?;
                }
                for (i, (name, value)) in named_args.iter().enumerate() {
                    if i > 0 || !args.is_empty() { write!(f, ", ")?; }
                    write!(f, "{} = {}", name, value)?;
                }
                write!(f, ")")
            }
            Expression::MemberAccess { object, member } => {
                write!(f, "{}.{}", object, member)
            }
            Expression::SpreadMember { object } => write!(f, "{}.{{...}}", object),
            Expression::Index { object, index } => write!(f, "{}[{}]", object, index),
            Expression::IfExpr { condition, then_branch, elif_branches, else_branch } => {
                write!(f, "if {} do {}", condition, then_branch)?;
                for (cond, branch) in elif_branches {
                    write!(f, " elif {} do {}", cond, branch)?;
                }
                if let Some(e) = else_branch {
                    write!(f, " else {}", e)?;
                }
                Ok(())
            }
            Expression::Comprehension { clauses, body } => {
                for clause in clauses {
                    match clause {
                        CompClause::For { pattern, iterables } => {
                            let iters = iterables.iter().map(|e| e.to_string())
                                .collect::<Vec<_>>().join(", ");
                            write!(f, "for {} in {} ", pattern, iters)?;
                        }
                    }
                }
                write!(f, "do {}", body)
            }
            Expression::TypeCheck { expression, type_expr } => {
                write!(f, "{}: {}", expression, type_expr)
            }
            Expression::Range { start, end } => {
                match (start, end) {
                    (Some(s), Some(e)) => write!(f, "{}..{}", s, e),
                    (Some(s), None) => write!(f, "{}..", s),
                    (None, Some(e)) => write!(f, "..{}", e),
                    (None, None) => write!(f, ".."),
                }
            }
            Expression::Pipeline { left, op, right } => {
                write!(f, "{} {} {}", left, op, right)
            }
        }
    }
}

impl fmt::Display for PipelineOperator {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = match self {
            PipelineOperator::Pipe => "|>",
            PipelineOperator::Map => "*>",
            PipelineOperator::Filter => "?>",
            PipelineOperator::Handle => "!>",
        };
        write!(f, "{}", s)
    }
}

impl fmt::Display for NumberLiteral {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = match self {
            NumberLiteral::Decimal(v) | NumberLiteral::Hex(v) | NumberLiteral::Binary(v)
            | NumberLiteral::Scientific(v) => v,
        };
        write!(f, "{}", s)
    }
}

impl fmt::Display for FStringPart {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            FStringPart::Text(content) => write!(f, "{}", content),
            FStringPart::Expression(expr, None) => write!(f, "{{{}}}", expr),
            FStringPart::Expression(expr, Some(spec)) => write!(f, "{{{}:{}}}", expr, spec),
        }
    }
}

impl fmt::Display for ObjectEntry {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ObjectEntry::KeyValue { key, value } => write!(f, "{}: {}", key, value),
            ObjectEntry::Shorthand(name) => write!(f, "{}", name),
            ObjectEntry::Spread => write!(f, "..."),
        }
    }
}

impl fmt::Display for BinaryOperator {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = match self {
            BinaryOperator::Add => "+",
            BinaryOperator::Sub => "-",
            BinaryOperator::Mul => "*",
            BinaryOperator::Div => "/",
            BinaryOperator::Mod => "%",
            BinaryOperator::Pow => "**",
            BinaryOperator::Eq => "==",
            BinaryOperator::Ne => "!=",
            BinaryOperator::Lt => "<",
            BinaryOperator::Le => "<=",
            BinaryOperator::Gt => ">",
            BinaryOperator::Ge => ">=",
            BinaryOperator::And => "and",
            BinaryOperator::Or => "or",
            BinaryOperator::TypeOr => "|",
            BinaryOperator::TypeAnd => "&",
            BinaryOperator::BitXor => "^",
            BinaryOperator::Shl => "<<",
            BinaryOperator::Shr => ">>",
            BinaryOperator::UShr => ">>>",
        };
        write!(f, "{}", s)
    }
}
