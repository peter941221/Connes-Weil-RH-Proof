"""Wrap generated Lean after symbol substitution, without changing tokens."""
import textwrap


def wrap_source(source):
    lines = []
    for line in source.splitlines():
        indent = len(line)-len(line.lstrip())
        lines.extend(textwrap.wrap(line,width=98,subsequent_indent=" "*(indent+4),
                                  break_long_words=False,break_on_hyphens=False) or [""])
    result = "\n".join(lines)+"\n"
    assert result.split() == source.split()
    assert max(map(len,result.splitlines()),default=0) <= 100
    return result
