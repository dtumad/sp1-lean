import SP1Clean.Model.Core.ProgramImage

/-! # Finite program-image validation regressions -/

namespace SP1CleanTest.Core.ProgramImage

open SP1Clean.Model.Core

private def image : ProgramImage :=
  ⟨[(65536, 0x00000073)], 65536, [(65536, 0x73), (65540, 42)]⟩

example : image.check.isSome = true := by native_decide

example : ({ image with entry := 65540 }).check.isSome = false := by native_decide

example : ({ image with rom := image.rom ++ image.rom }).check.isSome = false := by native_decide

example : ({ image with rom := [(65538, 0x73)] }).check.isSome = false := by native_decide

example : ({ image with rom := [(65536, 0x00)] }).check.isSome = false := by native_decide

example : ({ image with image := [(65536, 0xff)] }).check.isSome = false := by native_decide

example : ({ image with image := [(65540, 42), (65540, 42)] }).check.isSome = false := by native_decide

example : ({ image with image := [(2 ^ 48, 42)] }).check.isSome = false := by native_decide

example : image.initialMemory.readBytes 65536 6 = [0x73, 0, 0, 0, 42, 0] := by native_decide

example : [65535, 65536, 65539, 65540].map image.readOnly = [false, true, true, false] := by
  native_decide

end SP1CleanTest.Core.ProgramImage
