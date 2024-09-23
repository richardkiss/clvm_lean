import io
import shlex
import subprocess
import traceback

from pathlib import Path

from clvm import SExp
from clvm.serialize import sexp_to_byte_iterator, sexp_from_stream
from clvm_tools.binutils import assemble


MY_PATH = Path(__file__).parent

BRUN_PATH = MY_PATH / "../.lake/build/bin/Main"


SKIP_LIST = "softfork-4 unknown-0 unknown-1 unknown-2".split()


def from_hex(s: str) -> SExp:
    return sexp_from_stream(io.BytesIO(bytes.fromhex(s)), SExp.to)


def assembly_to_hex(prog_txt) -> str:
    return b"".join(sexp_to_byte_iterator(assemble(prog_txt))).hex()


def normalize_output(output: str, exp: str) -> (str, str):
    """
    The `brun` output is often disassembly, but sometimes it is hex.
    Let's normalize it to hex.

    When we `FAIL`, it's always disassembly.

    We have output of the form `FAIL: apply takes exactly 2 arguments ff1080`
    We want to strip off the hex and convert it to disassembly.
    """
    new_exp = exp
    if exp.startswith("FAIL") and output.startswith("FAIL"):
        parts = output.rsplit(" ", 1)
        if exp.startswith(parts[0]):
            exp_end = exp[len(parts[0]):]
            new_last_exp_part = assembly_to_hex(exp_end)
            new_exp = f"{parts[0]} {new_last_exp_part}"
    new_output = output

    return new_output, new_exp

def run_test(path: Path):
    if "zzint-0." in path.name:
        breakpoint()
    txt = path.read_text()
    both_hex, exp = parse_test(txt)
    if exp.startswith("FAIL: cost exceeded"):
        return
    # now, invoke command-line tool `brun` with both_hex as the argument, and capture the output
    r = subprocess.run([BRUN_PATH, both_hex], capture_output=True, text=True)
    output = r.stdout.strip()
    output, exp = normalize_output(output, exp)
    if output == exp:
        return
    print("-" * 80)
    print(f"{path}")
    print("TEST FAIL")
    print("contents:")
    print("===")
    print(txt)
    print("===")
    print(f"got {repr(output)}")
    print(f"expected {repr(exp)}")
    print("===")
    print("-" * 80)


STRIP_DICT = dict(c=1, n=1, strict=1, d=1, m=2, v=1)
STRIP_DICT.update({"backend=python" : 1})


def parse_test(txt: str) -> (str, str):
    lines = txt.split("\n")
    while lines[0].startswith("#"):
        del lines[0]
    if lines[1].startswith("cost"):
        del lines[1]
    command_line = lines[0]
    command = shlex.split(command_line)
    assert command[0] == "brun"
    command = command[1:]
    dump_as_hex = False
    while command[0].startswith("-"):
        flag = command[0]
        if flag == "-d":
            dump_as_hex = True
        while flag.startswith("-"):
            flag = flag[1:]
        if flag not in STRIP_DICT:
            print(flag)
            breakpoint()
        index = STRIP_DICT[flag]
        command = command[index:]
    # find the first single quote from the command line and excise everything before that
    prog_txt = command[0]
    args_txt = command[1] if len(command) > 1 else "()"
    prog_hex = assembly_to_hex(prog_txt)
    args_hex = assembly_to_hex(args_txt)
    if lines[1].startswith("FAIL") or dump_as_hex:
        exp = lines[1]
    else:
        exp = assembly_to_hex(lines[1])
    both_hex = f"ff{prog_hex}{args_hex}"
    return both_hex, exp


def test_brun():
    PATH = Path("/Users/kiss/projects/chia/clvm/main/tests/brun")
    all_paths = sorted(PATH.glob("*.txt"))
    for path in all_paths:
        if any(s in path.name for s in SKIP_LIST):
            continue
        try:
            run_test(path)
        except SyntaxError as e:
            pass
        except Exception as e:
            if e.msg == 'illegal dot expression at 3':
                # we don't care about these
                continue
            print("-" * 80)
            print(f"{path}")
            print("TEST FAIL EXCEPTION")
            print("contents:")
            print("===")
            print(path.read_text())
            print("===")
            print(f"Exception: {e}")
            # print exception back-trace
            print(traceback.format_exc())
            print("-" * 80)
