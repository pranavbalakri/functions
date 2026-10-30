module

public import VerifiedSqrt.Arm.Relocation
public import VerifiedSqrt.Arm.Registers64

@[expose] public section

namespace VerifiedSqrt.Arm

theorem Machine.readD_relocate (base : UInt64) (s : Machine) (r : Nat) :
    (s.relocate base).readD r = s.readD r := rfl

theorem Machine.relocate_writeD (base : UInt64) (s : Machine) (r : Nat) (w : UInt64) :
    (s.writeD r w).relocate base = (s.relocate base).writeD r w := rfl

theorem Machine.relocate_writeFP64 (base : UInt64) (s : Machine) (r : Nat) (w : FPResult64) :
    (s.writeFP64 r w).relocate base = (s.relocate base).writeFP64 r w := rfl

end VerifiedSqrt.Arm
