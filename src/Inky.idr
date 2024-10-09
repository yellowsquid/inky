module Inky

import Collie
import Control.App
import Control.App.Console
import Control.App.FileIO
import Inky.Context
import Inky.Parser
import Inky.Term
import Inky.Term.Parser
import Inky.Term.Pretty
import Inky.Thinning
import Inky.Type
import Inky.Type.Pretty
import System.File.Mode
import System.File.ReadWrite
import System.File.Virtual
import Text.Lexer
import Text.PrettyPrint.Prettyprinter
import Text.PrettyPrint.Prettyprinter.Render.Terminal

%default partial

%hide Collie.Modifiers.infix.(::=)

-- Actions ---------------------------------------------------------------------

lexInkyString : HasErr String es => String -> App es (List (WithBounds InkyToken))
lexInkyString file = do
  let (tokens, _, _, "") = lex tokenMap file
    | (_, line, col, rest) => throw "\{show (1 + line)}:\{show col}: unexpected character"
  pure (filter (\x => relevant x.val.kind) tokens)

parseType : HasErr String es => List (WithBounds InkyToken) -> App es (Ty [<] ())
parseType toks = do
  let Ok res [] _ = parse @{EqI} OpenType toks
    | Ok res (x :: _) _ => throw "\{x.bounds}: unexpected token \{x.val.kind}, expected end of input"
    | Err msg => throw msg
  let Right a = res.try [<]
    | Left msg => throw msg
  pure a

parseTerm : HasErr String es => List (WithBounds InkyToken) -> App es (CheckTerm [<] [<])
parseTerm toks = do
  let Ok res [] _ = parse @{EqI} OpenCheck toks
    | Ok res (x :: _) _ => throw "\{x.bounds}: unexpected token \{x.val.kind}, expected end of input"
    | Err msg => throw msg
  let Right t = res.try [<] [<]
    | Left msg => throw msg
  pure t

checkType : HasErr String es => Ty [<] () -> App es ()
checkType a = do
  let False = illFormed a
    | True => throw "type ill-formed"
  pure ()

checkTerm : HasErr String es => Ty [<] () -> CheckTerm [<] [<] -> App es ()
checkTerm a t = do
  let True = checks [<] [<] a t
    | False => throw "term ill-typed"
  pure ()

printType :
  PrimIO es => {default defaultLayoutOptions opts : LayoutOptions} ->
  Ty [<] () -> App es ()
printType a = do
  primIO $ renderIO $ layoutSmart opts $ prettyType a Open

printTerm :
  PrimIO es => {default defaultLayoutOptions opts : LayoutOptions} ->
  CheckTerm [<] [<] -> App es ()
printTerm a = do
  primIO $ renderIO $ layoutSmart opts $ prettyCheck a Open

readFile : FileIO es => File -> App es String
readFile f = do
  content <- read [<] f
  pure (fastConcat $ content <>> [])
  where
  read : SnocList String -> File -> App es (SnocList String)
  read acc f = do
    False <- fEOF f
      | True => pure acc
    str <- fGetStr f
    read (acc :< str) f

readFileOrStdin : FileIO es => HasErr IOError es => Maybe FilePath -> App es String
readFileOrStdin Nothing = readFile stdin
readFileOrStdin (Just path) = withFile path Read throw readFile


-- Arguments -------------------------------------------------------------------

Inky : Command "inky"
Inky = MkCommand
  { description = """
    tool suite for Primrose programs
    """
  , subcommands =
    [ "--help" ::= basic "print this help text" none
    , "format" ::= MkCommand
      { description = """
        pretty print data
        """
      , subcommands =
        [ "type" ::= basic "print a type" filePath
        , "term" ::= basic "print a term" filePath
        ]
      , modifiers = []
      , arguments = none
      }
    , "check" ::= MkCommand
      { description = """
        check well-formedness
        """
      , subcommands =
        [ "type" ::= basic "check a type" filePath
        , "term" ::= MkCommand
          { description = "check a term"
          , subcommands = []
          , modifiers = ["--type" ::= option "type to check against" filePath]
          , arguments = filePath
          }
        ]
      , modifiers = []
      , arguments = none
      }
    ]
  , modifiers = []
  , arguments = none
  }

-- Driver ----------------------------------------------------------------------

parseArgs :
  (cmd : Command nm) ->
  App (String :: Init) (ParseTree cmd)
parseArgs cmd = do
  Right args <- primIO cmd.parseArgs
    | Left msg => throw msg
  let Pure args = ParsedTree.finalising args
    | Fail errs => throw (show $ the (Error ()) $ Fail errs)
  pure args

abortErr : PrimIO es => String -> App es a
abortErr msg = do
  primIO $ () <$ fPutStrLn stderr msg
  primIO exitFailure

showHelp : Console es => App es ()
showHelp = putStrLn "Usage: \{Inky .usage}"

main : IO ()
main = run {l = MayThrow} $ do
  args <- handle {err = String} (parseArgs Inky) pure abortErr
  Collie.handle {cmd = ("inky" ** Inky)} args
    [ const showHelp
    , "--help" ::= [ const showHelp ]
    , "format" ::=
      [ const showHelp
      , "type" ::=
        [ \cmd => do
          let path = cmd.arguments
          txt <- handle {err = IOError} (readFileOrStdin path) pure (abortErr . show)
          toks <- handle {err = String} (lexInkyString txt) pure abortErr
          a <- handle {err = String} (parseType toks) pure abortErr
          printType a
          pure ()
        ]
      , "term" ::=
        [ \cmd => do
          let path = cmd.arguments
          txt <- handle {err = IOError} (readFileOrStdin path) pure (abortErr . show)
          toks <- handle {err = String} (lexInkyString txt) pure abortErr
          t <- handle {err = String} (parseTerm toks) pure abortErr
          printTerm t
          pure ()
        ]
      ]
    , "check" ::=
      [ const showHelp
      , "type" ::=
        [ \cmd => do
          let path = cmd.arguments
          txt <- handle {err = IOError} (readFileOrStdin path) pure (abortErr . show)
          toks <- handle {err = String} (lexInkyString txt) pure abortErr
          a <- handle {err = String} (parseType toks) pure abortErr
          handle {err = String} (checkType a) pure abortErr
        ]
      , "term" ::=
        [ \cmd => do
          let path = cmd.arguments
          txt <- handle {err = IOError} (readFileOrStdin path) pure (abortErr . show)
          toks <- handle {err = String} (lexInkyString txt) pure abortErr
          t <- handle {err = String} (parseTerm toks) pure abortErr
          let [type] = cmd.modifiers.content
          a <-
            maybe (pure (TArrow TNat TNat))
              (\path => do
                txt <- handle {err = IOError} (readFileOrStdin $ Just path) pure (abortErr . show)
                toks <- handle {err = String} (lexInkyString txt) pure abortErr
                a <- handle {err = String} (parseType toks) pure abortErr
                handle {err = String} (checkType a) pure abortErr
                pure a)
              type
          handle {err = String} (checkTerm a t) pure abortErr
        ]
      ]
    ]
