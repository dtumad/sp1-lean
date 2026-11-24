import SP1Clean.FormalModel.Contracts.StockPublicOutput
import SP1Clean.Math.SP1Field

/-! # Released SDK public-output regressions

Expected bytes are from the pinned Rust `SP1PublicValues::{hash, blake3_hash}` on messages
whose byte at offset `i` is `i % 251`. Cases straddle compression blocks, chunks and both
balanced and left-heavy BLAKE3 trees.
-/

namespace SP1CleanTest.Core.StockPublicOutput

open SP1Clean SP1Clean.FormalModel.StockPublicOutput

private def vectors : List (Nat × String × String) := [
  (0, "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855",
    "af1349b9f5f9a1a6a0404dea36dcc9499bcb25c9adc112b7cc9a93cae41f3262"),
  (1, "6e340b9cffb37a989ca544e6bb780a2c78901d3fb33738768511a30617afa01d",
    "2d3adedff11b61f14c886e35afa036736dcd87a74d27b5c1510225d0f592e213"),
  (63, "29af2686fd53374a36b0846694cc342177e428d1647515f078784d69cdb9e488",
    "e9bc37a594daad83be9470df7f7b3798297c3d834ce80ba85d6e207627b7db7b"),
  (64, "fdeab9acf3710362bd2658cdc9a29e8f9c757fcf9811603a8c447cd1d9151108",
    "4eed7141ea4a5cd4b788606bd23f46e212af9cacebacdc7d1f4c6dc7f2511b98"),
  (65, "4bfd2c8b6f1eec7a2afeb48b934ee4b2694182027e6d0fc075074f2fabb31781",
    "de1e5fa0be70df6d2be8fffd0e99ceaa8eb6e8c93a63f2d8d1c30ecb6b263dee"),
  (1023, "1c5e88a585b61754df6137d66632a7348557a88358afc401b0a0a4fc427104a9",
    "10108970eeda3eb932baac1428c7a2163b0e924c9a9e25b35bba72b28f70bd11"),
  (1024, "2bce1ba628720664be4b9fdd77aae0678e5f0f3f02fc6ff641ec879094f6a404",
    "42214739f095a406f3fc83deb889744ac00df831c10daa55189b5d121c855af7"),
  (1025, "bc0b6b10b89b9487a12fda2a8cc13194e7091c217aabf8b92846274026f4bcd0",
    "d00278ae47eb27b34faecf67b4fe263f82d5412916c1ffd97c8cb7fb814b8444"),
  (2048, "b2a8170614e23194ae2951423d601987f518ce2f11205d7b0b708080103b9f76",
    "e776b6028c7cd22a4d0ba182a8bf62205d2ef576467e838ed6f2529b85fba24a"),
  (2049, "26e1e2808e3a6cf967ca03f6749a063c5ed55f92f5874653a1faabed78346f00",
    "5f4d72f40d7a5f82b15ca2b2e44b1de3c2ef86c426c95c1af0b6879522563030"),
  (3072, "5f24b2f16026ec7d0450a5a08283d3cfd47302fe859f579ed79fe7d2663b73f9",
    "b98cb0ff3623be03326b373de6b9095218513e64f1ee2edd2525c7ad1e5cffd2"),
  (3073, "b870cdfe188c14fbfc31a1be12cd7e83b63551fff30f847fa275d5d4ac409471",
    "7124b49501012f81cc7f11ca069ec9226cecb8a2c850cfe644e327d22d3e1cd3"),
  (8193, "7e3691790cd64b19d4edb1a80e988214515abeb53aa0f34ffbfe4b4bf405d120",
    "bab6c09cb8ce8cf459261398d2e7aef35700bf488116ceb94a36d0f5f1b7bc3b")]

private def hex (digest : Vector (BitVec 8) 32) : String :=
  String.join (digest.toList.map BitVec.toHex)

example : vectors.all (fun (size, sha, blake) =>
    let bytes := (List.range size).map fun i => BitVec.ofNat 8 (i % 251)
    hex (sha256 bytes) == sha && hex (blake3 bytes) == blake) = true := by native_decide

example : (Claim.mk 0 (sha256 [10])).accepts [10] = true := by native_decide
example : (Claim.mk 0 (blake3 [10])).accepts [10] = true := by native_decide
example : (Claim.mk 0 (blake3 [10])).accepts [11] = false := by native_decide
example : (Claim.mk 1 (sha256 [])).accepts [] = false := by native_decide
example : (Claim.mk 1 (sha256 [])).accepts [] .panic true = true := by native_decide
example : ExpectedStatus.any.accepts false 3 = false := by decide
example : ExpectedStatus.any.accepts true 3 = true := by decide
example : ExpectedStatus.any.accepts true 2 = false := by decide
example : acceptsCore (p := SP1Prime) [] [] = false := by rfl

-- The SDK casts individual field limbs to bytes when reading the public record.
example : (ofFields (0 : ZMod SP1Prime) (Vector.replicate 8 #v[0x101, 0xff, 0x100, 0xabcd])).digest.toList.take 4 =
    [1, 255, 0, 205] := by native_decide

end SP1CleanTest.Core.StockPublicOutput
