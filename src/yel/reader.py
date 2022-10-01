from typing import *

import json
import ast

class ReaderError(Exception):
    pass

class EndOfFile(ReaderError):
    pass

def delimiter_p(c):
    return c and c in "\"()[]{},;\r\n"

def elisp_delimiter_p(c):
    return c and c in "\"()[],;\r\n"

def delimiter_fn(s):
    if stream_mode(s) == 'elisp':
        return elisp_delimiter_p
    return delimiter_p

def closing_p(c):
    return c and c in ")]}"

def elisp_closing_p(c):
    return c and c in ")]"

def closing_fn(s):
    if stream_mode(s) == 'elisp':
        return elisp_closing_p
    return closing_p

def whitespace_p(c):
    return c and c in " \t\r\n"

def end_of_input_p(c):
    return c is None

def looking_at(s, predicate):
    c = peek_char(s)
    return predicate(c) if callable(predicate) else c == predicate

def stream(string: str, start=0, end=None, more=None, mode=None):
    end = len(string) if end is None else end
    return [string, start, end, more, mode or "lisp"]

def stream_item(s, idx, *val):
    if val:
        s[idx] = val[0]
    return s[idx]

def stream_string(s, *val) -> str:
    return stream_item(s, 0, *val)

def stream_pos(s, *val) -> int:
    return stream_item(s, 1, *val)

def stream_end(s, *val) -> int:
    return stream_item(s, 2, *val)

def stream_more(s, *val) -> Any:
    return stream_item(s, 3, *val)

def stream_mode(s, *val) -> Any:
    return stream_item(s, 4, *val)

def forward_char(s, count=1):
    stream_pos(s, stream_pos(s) + count)

def peek_char(s, count=1, offset=0):
    pos = stream_pos(s) + offset
    if 0 <= pos + count <= stream_end(s):
        return stream_string(s)[pos:pos+count]

def read_char(s, count=1, offset=0):
    if c := peek_char(s, count=count, offset=offset):
        forward_char(s, count)
        return c

def read_line(s):
    r = []
    while (c := read_char(s)) and c != "\n":
        r.append(c)
    return ''.join(r) + "\n"

def skip_non_code(s):
    while c := peek_char(s):
        if whitespace_p(c):
            read_char(s)
        elif c == ";":
            read_line(s)
        else:
            break

def read_from_string(string, start=0, end=None, more=None, mode=None):
    s = stream(string, start=start, end=end, more=more, mode=mode)
    return read(s), stream_pos(s)

# (define read (s)
#   (let form (read-1 s)
#     (if (= "," (peek-char s))
#         (with r (list "," form)
#           (while true
#             (read-char s)
#             (set form (read-1 s))
#             (if (eof? s form) (return (expected s "tuple")))
#             (add r form)
#             (unless (= "," (peek-char s))
#               (break))))
#       form)))
def read(s, eof=None, start=None):
    form = read1(s, eof=eof, start=start)
    c = peek_char(s)
    if c == ":":
        read_char(s)
        return wrap(s, "%colon", form, start=start)
    if c and c in "([{.":
        e = wrap(s, "%snake", form, start=start)
        # print(e)
        return e
    if c == ",":
        eos = object()
        r = ["%tuple", form]
        while True:
            read_char(s)
            form = read1(s, eof=eos, start=start, form=r)
            if form is eos:
                return expected(s, "tuple", start)
            if form is not None:
                r.append(form)
            if peek_char(s) != ",":
                break
        return r
    return form

def read1(s, eof=None, start=None, form=None):
    skip_non_code(s)
    if start is None:
        start = stream_pos(s)
    c = peek_char(s)
    if c is None:
        return eof
    elif c == "(":
        form = read_list(s, "(", ")", start=start)
        if form == stream_more(s):
            return form
        # if len(form) == 1 and form[0] and isinstance(form[0], list) and form[0][0] in ["%tuple", "%colon"]:
        if len(form) == 1 and form[0] and isinstance(form[0], list) and form[0][0] in ["%tuple"]:
            return form[0]
        return form
    elif c == "[":
        form = read_list(s, "[", "]", start=start)
        if form == stream_more(s):
            return form
        # if stream_mode(s) in ["bel", "arc"]:
        #     return ["fn", ["_"], form]
        return ["%brackets", *form]
    elif c == "{" and stream_mode(s) != "elisp":
        return ["%braces", *read_list(s, "{", "}", start=start)]
    elif c == '"':
        if peek_char(s, 3) == '"""':
            form = read_string(s, '"""', '"""', backquote=True)
            expr = ast.literal_eval(form)
            return json.dumps(expr)
        return read_string(s, '"', '"', backquote=True)
    # elif c == "|":
    #     return read_string(s, "|", "|", False)
    elif c == "|":
        n = 1
        while peek_char(s, 1, n) == "|":
            n += 1
        open, close = "|" * n, "|" * n
        while (c := peek_char(s, 1, n)) in ["\r", "\n"]:
            open = open + c
            close = c + close
            n += 1
        form = read_string(s, open, close, backquote=True)
        if form == stream_more(s):
            return form
        expr = form[len(open):-len(close)]
        return "|" + expr + "|"
    elif c == "'":
        read_char(s)
        return wrap(s, "quote", start=start)
    elif c == "`":
        read_char(s)
        return wrap(s, "quasiquote", start=start)
    elif c == ("~" if stream_mode(s) == "clojure" else ","):
        read_char(s)
        if peek_char(s) == "@":
            read_char(s)
            return wrap(s, "unquote-splicing", start=start)
        return wrap(s, "unquote", start=start)
    elif closing_fn(s)(c):
        if form:
            # read_char(s)
            return
        raise SyntaxError(f"Unexpected {peek_char(s)!r} at {format_line_info(s, stream_pos(s))} from {format_line_info(s, start)}")
    return read_atom(s)

def read_all(s, *, verbose=False):
    out = []
    eof = object()
    if verbose:
        prev = stream_pos(s)
        import tqdm
        with tqdm.tqdm(total=stream_end(s), position=stream_pos(s)) as pbar:
            while (x := read(s, eof)) is not eof:
                out.append(x)
                pbar.update(stream_pos(s) - prev)
                prev = stream_pos(s)
    else:
        while (x := read(s, eof)) is not eof:
            out.append(x)
    return out

def line_info(s, pos: int):
    # s1 = stream(stream_string(s), end=stream_end(s))
    # line = 1
    # col = 1
    # while stream_pos(s1) < pos and (c := read_char(s1)):
    #     if c == "\n":
    #         col = 1
    #         line += 1
    #     else:
    #         col += 1
    lines = stream_string(s)[0:pos+1].splitlines(keepends=True)
    line = len(lines)
    col = len(lines[-1]) + 1
    return line, col

def format_line_info(s, pos: int):
    line, col = line_info(s, pos)
    return f"pos {pos} (line {line} column {col})"

def expected(s, c: str, start: int):
    if (more := stream_more(s)) is not None:
        return more
    raise EndOfFile(f"Expected {c!r} at {format_line_info(s, stream_pos(s))} from {format_line_info(s, start)}")

def read_list(s, open: str, close: str, start=None):
    if start is None:
        start = stream_pos(s)
    assert read_char(s) == open
    out = []
    skip_non_code(s)
    while (c := peek_char(s)) and c != close:
        out.append(read(s, start=start))
        skip_non_code(s)
    if c != close:
        return expected(s, close, start)
    assert read_char(s) == close
    # if len(out) == 1 and isinstance(out[0], list) and out[0] and out[0][0] == "%tuple":
    #     return out[0]
    return out

def read_atom(s, *, backquote: Optional[bool] = None):
    start = stream_pos(s)
    skip_non_code(s)
    while looking_at(s, whitespace_p) or looking_at(s, delimiter_fn(s)):
        read_char(s)
    out = []
    while c := peek_char(s):
        if backquote is not None:
            if c == '\\' or (stream_mode(s) == "elisp" and c == '?' and len(out) == 0):
                out.append(read_char(s))
                out.append(c1 := read_char(s) or expected(s, f"character after {c}", start))
                if c == '?' and c1 == '\\':
                    out.append(read_char(s) or expected(s, f"character after {c1}", start))
                continue
        if not c or whitespace_p(c) or delimiter_fn(s)(c):
            break
        out.append(read_char(s) or expected(s, "character", start))
    if (more := stream_more(s)) in out:
        return more
    form = "".join(out)
    if form.endswith(":") and form != ":":
        stream_pos(s, stream_pos(s) - 1)
        return form[:-1]
    return form

def read_string(s, open: str, close: str, *, backquote: Optional[bool] = None):
    start = stream_pos(s)
    assert read_char(s, len(open)) == open
    out = []
    n = len(close)
    while c := peek_char(s, n):
        if c == close:
            break
        if backquote is not None and c[0] == "\\":
            read_char(s)
            if backquote:
                out.append(c[0])
        out.append(read_char(s) or "")
    if c != close:
        return expected(s, close, start)
    assert read_char(s, n) == close
    return open + "".join(out) + close


def wrap(s, x, *rest, start=None):
    if (y := read(s, start=start)) == stream_more(s):
        return y
    else:
        if x == "%snake" and y and isinstance(y, list) and y[0] == "%snake":
            return [x, *rest, *y[1:]]
        return [x, *rest, y]



# s = reader.stream(open(os.path.expanduser("~/ml/bel/bel.bel")).read(), mode='bel'); bel = reader.read_all(s, verbose=True)
# s = reader.stream(open(os.path.expanduser("~/all-emacs.el")).read(), mode='elisp'); emacs = reader.read_all(s, verbose=True)