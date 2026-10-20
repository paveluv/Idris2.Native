||| How a file is opened (`OpenFlag`): the flags the OS service that opens
||| one takes (`Service.Open`), the same on every platform.
|||
||| The service takes them as one word, a bit for each flag present
||| (`bit`); each platform's module of the services gives each flag its
||| system's (`has`). The C library's modes are sets of them: `r` is
||| `ForReading`; `w` is `ForWriting`, `Create` and `Truncate`; `a` is
||| `ForWriting`, `Create` and `Append`; each with `+` the same and
||| `ForReading`.
|||
||| Part of the contract between compiled code and the runtime, with the
||| OS services (`Native.Service`).
module Native.OpenFlag

%default total

||| The flags a file is opened with.
public export
data OpenFlag
  = ||| Its bytes can be read.
    ForReading
  | ||| Bytes can be written to it.
    ForWriting
  | ||| It is made, empty, if nothing is at the path.
    Create
  | ||| It is emptied, if it was there.
    Truncate
  | ||| Each write goes to its end, wherever the last read left it.
    Append
  | ||| It is a directory, whose entries are read (`Service.ReadEntry`); it
    ||| is not opened if it is not one.
    ADirectory

||| The flag's bit in the word of the flags.
public export
bit : OpenFlag -> Bits64
bit ForReading = 1
bit ForWriting = 2
bit Create = 4
bit Truncate = 8
bit Append = 16
bit ADirectory = 32

||| Whether the word of the flags has the flag.
public export
has : OpenFlag -> (flags : Bits64) -> Bool
has f w = prim__and_Bits64 (bit f) w /= 0
