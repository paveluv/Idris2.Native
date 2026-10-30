||| Whether a stretch of bytes lies inside a buffer (`isInside`), which a
||| buffer's own reads and writes do not check where Idris's Chez code is
||| compiled unsafe.
module Native.Data.Inside

%default total

||| Whether the `k` bytes from `at` lie inside the `n` bytes from 0, `n` a
||| size, not below 0: `at` not below 0, and `k` not below 0 and no more
||| than the bytes past `at`, which puts `at` among the `n` bytes or just
||| past them. The count is compared with `n - at`, which no size and
||| offset wrap, not `at + k` with `n`, which could wrap past the largest
||| `Int`.
export
isInside : (n, at, k : Int) -> Bool
isInside n at k = 0 <= at && k <= n - at && 0 <= k
