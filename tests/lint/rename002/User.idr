||| A module that takes the token from `Token`: written bare, and qualified
||| by the module's name. Both are renamed, the qualifier kept. A string
||| that says `Tok` is no use of it, and stays.
module User

import Token

%default total

twice : Tok -> Nat
twice t = spend t + spend Token.MkTok

label : String
label = "Tok"
