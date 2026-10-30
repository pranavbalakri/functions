module

public import VerifiedSqrt.Arm.Sqrt32Code

public section

namespace VerifiedSqrt.Arm

theorem sqrt32_code_cases (word : UInt32) (hw : word ∈ sqrt32Code) :
    word = 0x1e260000 ∨
      word = 0x12007801 ∨
      word = 0x34000741 ∨
      word = 0x37f80740 ∨
      word = 0x52aff002 ∨
      word = 0x6b02001f ∨
      word = 0x540006c0 ∨
      word = 0x540006c8 ∨
      word = 0x52800004 ∨
      word = 0x53177801 ∨
      word = 0x350000e1 ∨
      word = 0x52aaf002 ∨
      word = 0x1e270041 ∨
      word = 0x1e210800 ∨
      word = 0x1e260000 ∨
      word = 0x53177801 ∨
      word = 0x128002e4 ∨
      word = 0x5101fc21 ∨
      word = 0x13017c22 ∨
      word = 0x0b020084 ∨
      word = 0x12000021 ∨
      word = 0x1101fc21 ∨
      word = 0x12005800 ∨
      word = 0x2a015c00 ∨
      word = 0x1e270000 ∨
      word = 0x1e2c1005 ∨
      word = 0x7ea1d801 ∨
      word = 0x1e210802 ∨
      word = 0x5ea1fc42 ∨
      word = 0x1e220821 ∨
      word = 0x1e210802 ∨
      word = 0x5ea1fc42 ∨
      word = 0x1e220821 ∨
      word = 0x1e210802 ∨
      word = 0x1e250823 ∨
      word = 0x1f028044 ∨
      word = 0x1f030880 ∨
      word = 0x53177802 ∨
      word = 0x51019842 ∨
      word = 0x12005803 ∨
      word = 0x52a01001 ∨
      word = 0x0b010063 ∨
      word = 0x9ac22063 ∨
      word = 0x1e260000 ∨
      word = 0x12005800 ∨
      word = 0x0b010000 ∨
      word = 0x0b000002 ∨
      word = 0x51000442 ∨
      word = 0x9ba27c42 ∨
      word = 0xeb02007f ∨
      word = 0x540001a3 ∨
      word = 0x0b000002 ∨
      word = 0x11000442 ∨
      word = 0x9ba27c42 ∨
      word = 0xeb02007f ∨
      word = 0x54000148 ∨
      word = 0x52a7e001 ∨
      word = 0x0b010000 ∨
      word = 0x0b045c00 ∨
      word = 0x1e270000 ∨
      word = 0xd65f03c0 ∨
      word = 0x7ea1d800 ∨
      word = 0xd65f03c0 ∨
      word = 0x51000400 ∨
      word = 0x17ffffee ∨
      word = 0x11000400 ∨
      word = 0x17ffffec := by
  simpa [sqrt32Code] using hw

end VerifiedSqrt.Arm
