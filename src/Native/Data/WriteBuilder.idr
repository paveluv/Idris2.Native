||| A text made of pieces written to a file a piece at a time
||| (`writeBuilder`, or `writeTo` an open file): a dump of a whole program
||| is never one string, nor a list of all its pieces, in memory at once
||| beside the builder.
module Native.Data.WriteBuilder

import Native.Data.Builder

import System.File.Error
import System.File.Handle
import System.File.Mode
import System.File.ReadWrite
import System.File.Types

%default covering

||| The pieces written to the open file, in order; or the first error,
||| after which nothing more is written.
export
writeTo : File -> Builder String -> IO (Either FileError ())
writeTo h b =
  foldlM (\ok, s => case ok of
                      Left err => pure (Left err)
                      Right () => fPutStr h s) (Right ()) b

||| The pieces written to the file at the path, in order, the file made or
||| emptied first; or the first error, after which nothing more is written.
export
writeBuilder : (path : String) -> Builder String -> IO (Either FileError ())
writeBuilder path b = do
  Right h <- openFile path WriteTruncate
    | Left err => pure (Left err)
  r <- writeTo h b
  closeFile h
  pure r
