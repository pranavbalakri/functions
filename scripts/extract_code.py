import argparse
import hashlib
from pathlib import Path
import struct
import subprocess

parser = argparse.ArgumentParser()
parser.add_argument("--check", action="store_true")
args = parser.parse_args()
root = Path(__file__).resolve().parent.parent
build = root / "build"
build.mkdir(exist_ok=True)
obj = build / "sqrt32.o"
subprocess.run(["clang", "-c", str(root / "asm/sqrt32.S"), "-o", str(obj)], check=True)
data = obj.read_bytes()
magic, cpu, subtype, kind, commands, size, flags, reserved = struct.unpack_from("<8I", data)
if magic != 0xfeedfacf or cpu != 0x100000c or kind != 1:
    raise SystemExit("expected an arm64 Mach-O object")
offset = 32
text = None
for _ in range(commands):
    command, length = struct.unpack_from("<II", data, offset)
    if command == 0x19:
        sections = struct.unpack_from("<I", data, offset + 64)[0]
        for i in range(sections):
            section = struct.unpack_from("<16s16sQQ8I", data, offset + 72 + 80 * i)
            if section[0].rstrip(b"\0") == b"__text":
                if section[7] != 0:
                    raise SystemExit("text contains relocations")
                text = data[section[4]:section[4] + section[3]]
    offset += length
if text is None or len(text) % 4:
    raise SystemExit("missing or malformed text section")
words = struct.unpack("<" + "I" * (len(text) // 4), text)
if any((w & 0xfffffc00) in (0x1e21c000, 0x1e61c000) for w in words):
    raise SystemExit("FSQRT found in routine")
lean = "module\n\npublic import Std\n\nnamespace VerifiedSqrt.Arm\n\n"
lean += "@[expose] public def sqrt32Code : Array UInt32 := #[\n"
lean += ",\n".join("  " + ", ".join(f"0x{w:08x}" for w in words[i:i + 4]) for i in range(0, len(words), 4))
lean += "\n]\n\nend VerifiedSqrt.Arm\n"
outputs = {
    root / "asm/sqrt32.bin": text,
    root / "VerifiedSqrt/Arm/Sqrt32Code.lean": lean.encode(),
}
for path, content in outputs.items():
    if args.check:
        if not path.exists() or path.read_bytes() != content:
            raise SystemExit(f"stale generated file: {path}")
    else:
        path.write_bytes(content)
listing = subprocess.check_output(["otool", "-tvV", str(obj)], text=True)
(build / "sqrt32.disasm").write_text(listing)
print(f"instructions={len(words)} bytes={len(text)} sha256={hashlib.sha256(text).hexdigest()} fsqrt=false")
