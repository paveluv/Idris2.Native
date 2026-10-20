||| The C library's messages for its error numbers (`errorMessage`), which
||| `strerror` gives: glibc's, for Linux's numbers, as `System.Errno`
||| gives them, a table computed when a program that uses it is compiled.
module Native.System.ErrorMessage

-- lint: allow public-import: the table's type reduces only where its
-- reading is visible, so it is wherever this module is
import public Native.Table

import Native.Flat.Uniform as Flat
import Native.Runtime.Alloc.Block as Runtime.Alloc
import Native.Runtime.Memory
import Native.Runtime.Ordo as Runtime
import Native.Runtime.Raw as Runtime
import Native.Support.Text

%hide Prelude.Interfaces.(>>=)
%hide Prelude.Interfaces.(>>)
%hide Prelude.Interfaces.pure

%default total

||| The words of a message: so many each, its bytes in them from the first
||| word's low byte, zero after; seven, for the longest message's 49 bytes.
rowWords : Int
rowWords = 7

||| Word `k mod 7` of the message for the error number `k div 7`; zero
||| words for a number of no message.
export covering
errorText : Table 0 937 Bits64
errorText k _ = wordOf (cast (8 * (k `mod` rowWords))) 8 (message (k `div` rowWords))
  where
    -- `n` bytes of the message from its character `skip`, the first the
    -- low one, zero past its end
    wordOf : (skip, n : Nat) -> String -> Bits64
    wordOf _ Z _ = 0
    wordOf skip (S j) s = case strUncons s of
      Nothing => 0
      Just (c, rest) => case skip of
        S skip' => wordOf skip' (S j) rest
        Z => cast (ord c) + prim__shl_Bits64 (wordOf Z j rest) 8

    message : Int -> String
    message 0 = "Success"
    message 1 = "Operation not permitted"
    message 2 = "No such file or directory"
    message 3 = "No such process"
    message 4 = "Interrupted system call"
    message 5 = "Input/output error"
    message 6 = "No such device or address"
    message 7 = "Argument list too long"
    message 8 = "Exec format error"
    message 9 = "Bad file descriptor"
    message 10 = "No child processes"
    message 11 = "Resource temporarily unavailable"
    message 12 = "Cannot allocate memory"
    message 13 = "Permission denied"
    message 14 = "Bad address"
    message 15 = "Block device required"
    message 16 = "Device or resource busy"
    message 17 = "File exists"
    message 18 = "Invalid cross-device link"
    message 19 = "No such device"
    message 20 = "Not a directory"
    message 21 = "Is a directory"
    message 22 = "Invalid argument"
    message 23 = "Too many open files in system"
    message 24 = "Too many open files"
    message 25 = "Inappropriate ioctl for device"
    message 26 = "Text file busy"
    message 27 = "File too large"
    message 28 = "No space left on device"
    message 29 = "Illegal seek"
    message 30 = "Read-only file system"
    message 31 = "Too many links"
    message 32 = "Broken pipe"
    message 33 = "Numerical argument out of domain"
    message 34 = "Numerical result out of range"
    message 35 = "Resource deadlock avoided"
    message 36 = "File name too long"
    message 37 = "No locks available"
    message 38 = "Function not implemented"
    message 39 = "Directory not empty"
    message 40 = "Too many levels of symbolic links"
    message 42 = "No message of desired type"
    message 43 = "Identifier removed"
    message 44 = "Channel number out of range"
    message 45 = "Level 2 not synchronized"
    message 46 = "Level 3 halted"
    message 47 = "Level 3 reset"
    message 48 = "Link number out of range"
    message 49 = "Protocol driver not attached"
    message 50 = "No CSI structure available"
    message 51 = "Level 2 halted"
    message 52 = "Invalid exchange"
    message 53 = "Invalid request descriptor"
    message 54 = "Exchange full"
    message 55 = "No anode"
    message 56 = "Invalid request code"
    message 57 = "Invalid slot"
    message 59 = "Bad font file format"
    message 60 = "Device not a stream"
    message 61 = "No data available"
    message 62 = "Timer expired"
    message 63 = "Out of streams resources"
    message 64 = "Machine is not on the network"
    message 65 = "Package not installed"
    message 66 = "Object is remote"
    message 67 = "Link has been severed"
    message 68 = "Advertise error"
    message 69 = "Srmount error"
    message 70 = "Communication error on send"
    message 71 = "Protocol error"
    message 72 = "Multihop attempted"
    message 73 = "RFS specific error"
    message 74 = "Bad message"
    message 75 = "Value too large for defined data type"
    message 76 = "Name not unique on network"
    message 77 = "File descriptor in bad state"
    message 78 = "Remote address changed"
    message 79 = "Can not access a needed shared library"
    message 80 = "Accessing a corrupted shared library"
    message 81 = ".lib section in a.out corrupted"
    message 82 = "Attempting to link in too many shared libraries"
    message 83 = "Cannot exec a shared library directly"
    message 84 = "Invalid or incomplete multibyte or wide character"
    message 85 = "Interrupted system call should be restarted"
    message 86 = "Streams pipe error"
    message 87 = "Too many users"
    message 88 = "Socket operation on non-socket"
    message 89 = "Destination address required"
    message 90 = "Message too long"
    message 91 = "Protocol wrong type for socket"
    message 92 = "Protocol not available"
    message 93 = "Protocol not supported"
    message 94 = "Socket type not supported"
    message 95 = "Operation not supported"
    message 96 = "Protocol family not supported"
    message 97 = "Address family not supported by protocol"
    message 98 = "Address already in use"
    message 99 = "Cannot assign requested address"
    message 100 = "Network is down"
    message 101 = "Network is unreachable"
    message 102 = "Network dropped connection on reset"
    message 103 = "Software caused connection abort"
    message 104 = "Connection reset by peer"
    message 105 = "No buffer space available"
    message 106 = "Transport endpoint is already connected"
    message 107 = "Transport endpoint is not connected"
    message 108 = "Cannot send after transport endpoint shutdown"
    message 109 = "Too many references: cannot splice"
    message 110 = "Connection timed out"
    message 111 = "Connection refused"
    message 112 = "Host is down"
    message 113 = "No route to host"
    message 114 = "Operation already in progress"
    message 115 = "Operation now in progress"
    message 116 = "Stale file handle"
    message 117 = "Structure needs cleaning"
    message 118 = "Not a XENIX named type file"
    message 119 = "No XENIX semaphores available"
    message 120 = "Is a named type file"
    message 121 = "Remote I/O error"
    message 122 = "Disk quota exceeded"
    message 123 = "No medium found"
    message 124 = "Wrong medium type"
    message 125 = "Operation canceled"
    message 126 = "Required key not available"
    message 127 = "Key has expired"
    message 128 = "Key has been revoked"
    message 129 = "Key was rejected by service"
    message 130 = "Owner died"
    message 131 = "State not recoverable"
    message 132 = "Operation not possible due to RF-kill"
    message 133 = "Memory page has hardware error"
    message _ = ""

||| The message for the error number, as glibc's `strerror` gives it:
||| "Unknown error" and the number for one it has none for.
export covering
errorMessage : (errno : Int) -> Runtime.Ordo.Op Runtime.Ordo (Flat.Uniform String)
errorMessage n =
  Runtime.Alloc.Block.allocate blockBytes Support.Text.emptyText (\b => do
    let Runtime.Alloc.Block.MkAddressed p b' = Runtime.Alloc.Block.address b
    len <- written p
    s <- Support.Text.ofText p len
    Runtime.Alloc.Block.free b'
    Runtime.Ordo.pure s)
  where
    -- the message's bytes, in a row's words, or "Unknown error " and the
    -- number's at most 20 bytes at the end
    blockBytes : Bits64
    blockBytes = 8 * cast rowWords + 32

    -- the row's words from the table's word `i`, the row's first `r`
    covering
    row : Runtime.Raw -> (r, i : Int) -> Runtime.Ordo.Op Runtime.Ordo ()
    row p r i with (0 <= i && i <= 937) proof inside
      _ | True = if i >= r + rowWords then Runtime.Ordo.pure () else do
        Runtime.Memory.storeAt p (cast (8 * (i - r))) (errorText i inside)
        row p r (i + 1)
      _ | False = Runtime.Ordo.pure ()

    -- the bytes up to the first zero byte from `i`
    covering
    textBytes : Runtime.Raw -> Bits64 -> Runtime.Ordo.Op Runtime.Ordo Bits64
    textBytes p i = if i >= cast (8 * rowWords) then Runtime.Ordo.pure i else do
      c <- Runtime.Memory.loadByteAt p i
      if c == 0 then Runtime.Ordo.pure i else textBytes p (i + 1)

    -- the decimal digits of `v` written backwards from `i` down; where the
    -- first digit is
    covering
    digits : Runtime.Raw -> (i, v : Bits64) -> Runtime.Ordo.Op Runtime.Ordo Bits64
    digits p i v = do
      Runtime.Memory.storeByteAt p i (0x30 + v `mod` 10)
      if v < 10 then Runtime.Ordo.pure i else digits p (i - 1) (v `div` 10)

    -- "Unknown error " and the number, written at the start; their bytes
    covering
    unknown : Runtime.Raw -> Runtime.Ordo.Op Runtime.Ordo Bits64
    unknown p = do
      -- "Unknown " and "error ", eight bytes and six
      Runtime.Memory.storeAt p 0 0x206E776F6E6B6E55
      Runtime.Memory.storeAt p 8 0x20726F727265
      if n < 0 then Runtime.Memory.storeByteAt p 14 0x2D else Runtime.Ordo.pure ()
      let at : Bits64 = if n < 0 then 15 else 14
          magnitude : Bits64 = if n < 0 then 0 - cast n else cast n
      first <- digits p (blockBytes - 1) magnitude
      Runtime.Memory.copyRaw (Runtime.Raw.offset p first) (Runtime.Raw.offset p at)
        (blockBytes - first)
      Runtime.Ordo.pure (at + blockBytes - first)

    ||| The last error number of a message, Linux's: the table is of 134
    ||| rows, 0 to 133, of `rowWords` each, its words 0 to 937.
    lastNumber : Int
    lastNumber = 133

    covering
    written : Runtime.Raw -> Runtime.Ordo.Op Runtime.Ordo Bits64
    written p =
      if n < 0 || n > lastNumber then unknown p else do
        row p (rowWords * n) (rowWords * n)
        len <- textBytes p 0
        if len == 0 then unknown p else Runtime.Ordo.pure len
