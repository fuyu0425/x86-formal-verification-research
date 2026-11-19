import Differential.Run
/-!
# The two inputs of the blog post's bugs
-/
namespace Differential
open ZellicX86

/-- `__memrchr_evex`'s bug: `s = 0x10000 * 4096 + 1`, `n = 2 ^ 32`, the object's last byte (at `0x110000000`, the
first byte of its page) the only `c = 'A'`; the object spans the `2 ^ 20 + 1` pages from page `0x10000`. -/
def evexInput : Input where
  objPage := 0x10000
  objPages := 2 ^ 20 + 1
  obj a := if a = 0x110000000 then 0x41 else 0
  s := 0x10000001
  c := 0x41
  n := 2 ^ 32

/-- `__memrchr_avx2`'s bug: page 0 mapped, `s = 5`, `n = 140`, no byte of page 0 is `c = 'A'`. -/
def avx2Input : Input where
  objPage := 0
  objPages := 1
  obj _ := 0
  s := 5
  c := 0x41
  n := 140

end Differential
