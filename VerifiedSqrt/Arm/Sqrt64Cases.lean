module

public import VerifiedSqrt.Arm.Sqrt64Code

public section

namespace VerifiedSqrt.Arm

theorem sqrt64_code_cases (word : UInt32) (hw : word ∈ sqrt64Code) :
    word = 0x9e660000 ∨
      word = 0x9240f801 ∨
      word = 0xb4000901 ∨
      word = 0xb7f80900 ∨
      word = 0xd2effe02 ∨
      word = 0xeb02001f ∨
      word = 0x54000880 ∨
      word = 0x54000888 ∨
      word = 0x52800004 ∨
      word = 0xd374f801 ∨
      word = 0xb50000e1 ∨
      word = 0xd2e8d202 ∨
      word = 0x9e670041 ∨
      word = 0x1e610800 ∨
      word = 0x9e660000 ∨
      word = 0xd374f801 ∨
      word = 0x12800684 ∨
      word = 0x510ffc21 ∨
      word = 0x13017c22 ∨
      word = 0x0b020084 ∨
      word = 0x12000021 ∨
      word = 0x110ffc21 ∨
      word = 0x9240cc00 ∨
      word = 0xaa01d000 ∨
      word = 0x9e670000 ∨
      word = 0x1e6c1005 ∨
      word = 0x7ee1d801 ∨
      word = 0x1e610802 ∨
      word = 0x5ee1fc42 ∨
      word = 0x1e620821 ∨
      word = 0x1e610802 ∨
      word = 0x5ee1fc42 ∨
      word = 0x1e620821 ∨
      word = 0x1e610802 ∨
      word = 0x5ee1fc42 ∨
      word = 0x1e620821 ∨
      word = 0x1e610802 ∨
      word = 0x1e650823 ∨
      word = 0x1f428044 ∨
      word = 0x1f430880 ∨
      word = 0xd374f802 ∨
      word = 0x510f2442 ∨
      word = 0x9240cc03 ∨
      word = 0xd2e00201 ∨
      word = 0x8b010063 ∨
      word = 0x52800806 ∨
      word = 0x4b0200c6 ∨
      word = 0x9ac62465 ∨
      word = 0x9ac22063 ∨
      word = 0x9e660000 ∨
      word = 0x9240cc00 ∨
      word = 0x8b010000 ∨
      word = 0x8b000002 ∨
      word = 0xd1000442 ∨
      word = 0x9bc27c46 ∨
      word = 0x9b027c42 ∨
      word = 0xeb0600bf ∨
      word = 0x54000283 ∨
      word = 0x54000068 ∨
      word = 0xeb02007f ∨
      word = 0x54000223 ∨
      word = 0x8b000002 ∨
      word = 0x91000442 ∨
      word = 0x9bc27c46 ∨
      word = 0x9b027c42 ∨
      word = 0xeb0600bf ∨
      word = 0x540001a8 ∨
      word = 0x54000063 ∨
      word = 0xeb02007f ∨
      word = 0x54000148 ∨
      word = 0xd2e7fc01 ∨
      word = 0x8b010000 ∨
      word = 0x8b04d000 ∨
      word = 0x9e670000 ∨
      word = 0xd65f03c0 ∨
      word = 0x7ee1d800 ∨
      word = 0xd65f03c0 ∨
      word = 0xd1000400 ∨
      word = 0x17ffffe6 ∨
      word = 0x91000400 ∨
      word = 0x17ffffe4 := by
  simpa [sqrt64Code] using hw

end VerifiedSqrt.Arm
