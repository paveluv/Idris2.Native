||| How far allocation may run past the allocation limit (`allocationMargin`):
||| whenever generated code runs, the runtime keeps the heap's memory
||| committed this many bytes past the limit. So code may bump the
||| allocation pointer past the limit by up to the margin before it checks
||| the pointer against the limit, and a primitive that allocates in
||| between finds the memory past the limit committed too.
|||
||| Part of the contract between compiled code and the runtime, as
||| `Native.Area` is, and like it of neither: it imports nothing, so that
||| the runtime's own Idris can import it.
module Native.AllocationMargin

%default total

||| The bytes committed past the allocation limit: 8 KiB, two pages, more
||| than a continuation of a thousand live values holds.
public export
allocationMargin : Bits64
allocationMargin = 8192
