#!/usr/bin/env python3
"""Sort the Bend prelude so every def precedes its callers (Bend has no
forward references) and report mutual recursion, which Bend rejects.

    python3 tools/prelude_sort.py src/prelude.bend
"""
import re
import sys

path = sys.argv[1]
text = open(path).read()


def mark_pattern_fields(text):
    """Add `+` to `case K{a, b}` binders used more than once in the arm."""
    out = []
    lines = text.split('\n')
    for i, l in enumerate(lines):
        m = re.match(r'^(\s*)case (.*):$', l)
        if not m:
            out.append(l)
            continue
        indent = len(m.group(1))
        # the arm body: following lines deeper than the case line, up to the next case at this indent or shallower
        body = []
        for l2 in lines[i + 1:]:
            if l2.strip() == '':
                body.append(l2)
                continue
            ind = len(l2) - len(l2.lstrip(' '))
            if ind <= indent:
                break
            body.append(l2)
        body_text = '\n'.join(x for x in body if not x.strip().startswith('#'))
        pats = m.group(2)

        def fix_field(fm):
            mark, name = fm.group(1), fm.group(2)
            if mark or name == '_':
                return fm.group(0)
            cnt = len(re.findall(r'(?<![A-Za-z0-9_.])' + re.escape(name) + r'(?![A-Za-z0-9_])', body_text))
            return ('+' if cnt > 1 else '') + name

        # binders inside {...} and the `h <> t` sugar
        def fix_ctor(cm):
            inner = re.sub(r'(\+?)([A-Za-z_][A-Za-z0-9_]*)', fix_field, cm.group(2))
            return cm.group(1) + '{' + inner + '}'

        pats2 = re.sub(r'([A-Za-z0-9_.]+)\{([^}]*)\}', fix_ctor, pats)
        pats2 = re.sub(r'(?<![A-Za-z0-9_.{])(\+?)([a-z][A-Za-z0-9_]*)(?= <> )', fix_field, pats2)
        pats2 = re.sub(r'(?<=<> )(\+?)([a-z][A-Za-z0-9_]*)', fix_field, pats2)
        out.append(m.group(1) + 'case ' + pats2 + ':')
    return '\n'.join(out)


text = mark_pattern_fields(text)
lines = text.split('\n')

blocks = []
cur = []
pending = []
header = []
i = 0
while i < len(lines):
    l = lines[i]
    if l.startswith('def ') or l.startswith('type ') or l.startswith('@unsafe'):
        if cur:
            blocks.append(cur)
        cur = pending + [l]
        pending = []
        i += 1
        if l.startswith('@unsafe'):
            cur.append(lines[i])
            i += 1
        while i < len(lines):
            if lines[i] == '':
                j = i
                while j < len(lines) and lines[j] == '':
                    j += 1
                if j < len(lines) and lines[j].startswith(' '):
                    cur.append(lines[i])
                    i += 1
                    continue
                break
            if not lines[i].startswith(' '):
                break
            cur.append(lines[i])
            i += 1
        continue
    if l.startswith('#'):
        if not cur and not blocks:
            header.append(l)
        else:
            pending.append(l)
        i += 1
        continue
    i += 1
if cur:
    blocks.append(cur)


def name_of(b):
    for l in b:
        m = re.match(r'(?:def|type) ([A-Za-z0-9_.]+)', l)
        if m:
            return m.group(1)
    return None


names = {name_of(b): k for k, b in enumerate(blocks)}


def deps(b):
    body = '\n'.join(l for l in b if not l.startswith('#'))
    me = name_of(b)
    out = set()
    for r in set(re.findall(r'\b(F\.[A-Za-z0-9_.]+)', body)):
        if r in names and r != me:
            out.add(r)
    return out


order = []
state = {}
stack = []


def visit(n):
    if state.get(n) == 2:
        return
    if state.get(n) == 1:
        cyc = stack[stack.index(n):] + [n]
        sys.exit('mutual recursion in the prelude: ' + ' -> '.join(cyc))
    state[n] = 1
    stack.append(n)
    for d in sorted(deps(blocks[names[n]])):
        visit(d)
    stack.pop()
    state[n] = 2
    order.append(n)


for b in blocks:
    visit(name_of(b))

out = header + ['']
for n in order:
    out.extend(blocks[names[n]])
    out.append('')
open(path, 'w').write('\n'.join(out).rstrip('\n') + '\n')
print(f'{len(blocks)} blocks, sorted')
