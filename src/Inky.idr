module Inky

import Collie

import Control.App
import Control.App.Console
import Control.App.FileIO

import Data.String

import Flap.Decidable
import Flap.Decidable.Maybe
import Flap.Parser

import Inky.Term
import Inky.Term.Checks
import Inky.Term.Compile
import Inky.Term.Desugar
import Inky.Term.Parser
import Inky.Term.Pretty
import Inky.Term.Pretty.Error
import Inky.Type.Pretty

import System.File.Mode
import System.File.ReadWrite
import System.File.Virtual

import Text.Lexer
import Text.PrettyPrint.Prettyprinter
import Text.PrettyPrint.Prettyprinter.Render.Terminal

%default partial

%hide Collie.Modifiers.infix.(::=)

record Erased (a : Type) where
  constructor Forget
  0 value : a

record SynthFailed where
  constructor UhOh
  term : Term NoSugar Bounds [<] [<]
  err : NotSynths {m = Bounds} [<] [<] term

Err : Type
Err = List1 (WithBounds String)

Interpolation Bounds where
  interpolate b =
    "\{show (1 + b.startLine)}:\{show (1 + b.startCol)}--\{show (1 + b.endLine)}:\{show (1 + b.endCol)}"

Interpolation a => Interpolation (WithBounds a) where
  interpolate x =
    if x.isIrrelevant
    then "?:?--?:?: \{x.val}"
    else "\{x.bounds}: \{x.val}"

-- Actions ---------------------------------------------------------------------

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

lexInkyString : HasErr (WithBounds String) es => String -> App es (List (WithBounds InkyToken))
lexInkyString file = do
  let (tokens, _, _, "") = lex tokenMap file
    | (_, line, col, rest) =>
      throw (MkBounded "unexpected character" False (MkBounds line col line col))
  pure (filter (\x => relevant x.val.kind) tokens)

Interpolation (List InkyKind) where
  interpolate [t] = interpolate t
  interpolate ts = "one of " ++ joinBy ", " (map interpolate ts)

doParse :
  HasErr (WithBounds String) es =>
  (p : InkyParser False [<] [<] a) ->
  {auto 0 wf : collectTypeErrs @{ListSet} [<] [<] [<] [<] p = []} ->
  List (WithBounds InkyToken) ->
  App es a
doParse p toks =
  case parse @{ListSet} p toks of
    Ok res [] _ => pure res
    Ok res (x :: _) _ =>
      throw ("expected end of input; got token \{x.val.kind}" <$ x)
    Err err => throw (parseErrToString err)
  where
  parseErrToString : ParseErr InkyKind -> WithBounds String
  parseErrToString (BadEOF ts) =
    irrelevantBounds "expected \{ts}; got end of input"
  parseErrToString (Unexpected ts got) =
    "expected \{ts}; got token \{got.val.kind}" <$ got

parseType :
  Has [HasErr (WithBounds String), HasErr Err, HasErr IOError, FileIO] es =>
  Maybe FilePath -> App es (Ty [<])
parseType path = do
  txt <- readFileOrStdin path
  toks <- lexInkyString txt
  res <- doParse OpenType toks
  let Ok a = res.try [<]
    | Errs errs => throw errs
  pure a

parseTerm :
  Has [HasErr (WithBounds String), HasErr Err, HasErr IOError, FileIO] es =>
  (termPath, tyPath : Maybe FilePath) -> App es (Term (Sugar [<]) Bounds [<] [<])
parseTerm termPath tyPath = do
  txt <- readFileOrStdin termPath
  toks <- lexInkyString txt
  res <- doParse OpenTerm toks
  let Ok t = res.try (Sugar [<]) [<] [<]
    | Errs errs => throw errs
  -- Annotate with type
  let Just _ = tyPath
    | Nothing => pure t
  a <- parseType tyPath
  pure (Annot (MkBounds 0 0 0 0) t a)

checkType : HasErr String es => (a : Ty [<]) -> App es ()
checkType a =
  unless (wellFormed a).does $
    throw "type ill-formed"

synthTerm :
  (t : Term NoSugar Bounds [<] [<]) ->
  HasErr SynthFailed es =>
  App es (Subset (Ty [<]) (Synths [<] [<] t))
synthTerm t = do
  let Just a `Because` prf = synths [<] [<] t
    | Nothing `Because` contra => throw (UhOh t contra)
  pure (Element a prf)

printType :
  PrimIO es => {default defaultLayoutOptions opts : LayoutOptions} ->
  Ty [<] -> App es ()
printType a = do
  primIO $ renderIO $ layoutSmart opts $ prettyType a Open

printTerm :
  PrimIO es => {default defaultLayoutOptions opts : LayoutOptions} ->
  {mode : Term.Mode} -> Term mode m [<] [<] -> App es ()
printTerm a = do
  primIO $ renderIO $ layoutSmart opts $ prettyTerm a Open

compileTerm :
  PrimIO es => {default defaultLayoutOptions opts : LayoutOptions} ->
  {t : Term NoSugar m [<] [<]} ->
  (0 prf : Synths [<] [<] t a) ->
  App es ()
compileTerm prf =
  primIO $ renderIO $ layoutSmart opts $
  pretty "(use-modules (ice-9 match))" <+> line <+>
  parens (hang 1 $ pretty "define main" <+> line <+> group (compileSynths [<] [<] prf))


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
        , "term" ::= MkCommand
          { description = "print a term"
          , subcommands = []
          , modifiers = ["--desugar" ::= flag "desugar the term"]
          , arguments = filePath
          }
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
    , "compile" ::= MkCommand
      { description = """
        compile to scheme
        """
      , subcommands =
        [ "term" ::= MkCommand
          { description = "compile a term"
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

showHelp : Console es => App es ()
showHelp = putStrLn "Usage: \{Inky .usage}"

process :
  Has
    [ HasErr String
    , HasErr (WithBounds String)
    , HasErr (List1 $ WithBounds String)
    , HasErr (List1 ErrorMsg)
    , HasErr SynthFailed
    , FileIO
    , PrimIO
    ] es =>
  App es ()
process = do
  Right args <- primIO (Inky).parseArgs
    | Left msg => throw msg
  let Pure args = ParsedTree.finalising args
    | Fail errs => throw errs
  Collie.handle {cmd = ("inky" ** Inky)} args
    [ const showHelp
    , "--help" ::= [ const showHelp ]
    , "format" ::=
      [ const showHelp
      , "type" ::=
        [ \cmd => do
          let path = cmd.arguments
          a <- parseType path
          printType a
        ]
      , "term" ::=
        [ \cmd => do
          let path = cmd.arguments
          t <- parseTerm path Nothing
          let [noSugar] = cmd.modifiers.content
          case noSugar of
            True => printTerm (desugar t)
            False => printTerm t
        ]
      ]
    , "check" ::=
      [ const showHelp
      , "type" ::=
        [ \cmd => do
          let path = cmd.arguments
          a <- parseType path
          _ <- checkType a
          pure ()
        ]
      , "term" ::=
        [ \cmd => do
          let path = cmd.arguments
          let [type] = cmd.modifiers.content
          t <- parseTerm path type
          let t = desugar t
          _ <- synthTerm t
          pure ()
        ]
      ]
    , "compile" ::=
      [ const showHelp
      , "term" ::=
        [ \cmd => do
          let path = cmd.arguments
          let [type] = cmd.modifiers.content
          t <- parseTerm path type
          let t = desugar t
          Element _ prf <- synthTerm t
          compileTerm prf
        ]
      ]
    ]

handleErr : (0 e : Type) -> (forall a. e -> App es a) -> App (e :: es) a -> App es a
handleErr e handler app = handle app pure handler

printSynthFailed :
  PrimIO es => {default defaultLayoutOptions opts : LayoutOptions} ->
  SynthFailed -> App es ()
printSynthFailed (UhOh t err) =
  primIO $ renderIO $ layoutSmart opts $
  concatWith (surround hardline) $
  map (\(bounds, msg) => group $ align $ hang 2 $ pretty "\{bounds}:" <+> line <+> msg) $
  prettyNotSynths err

main : IO ()
main =
  run {l = MayThrow} $
  handleErr (List String)
    (\msgs => do
      foldlM (\_, msg => primIO $ () <$ fPutStrLn stderr msg) () msgs
      primIO exitFailure) $
  handleErr String
    (throw . List.singleton) $
  handleErr (List1 ErrorMsg)
    (throw . map show . forget) $
  handleErr (List1 $ WithBounds String)
    (throw . map interpolate . forget) $
  handleErr (WithBounds String)
    (throw . (::: [])) $
  handleErr IOError
    (throw . show) $
  handleErr SynthFailed
    (\err => do
      printSynthFailed err
      primIO exitFailure) $
  process

-- main =
--   run {l = MayThrow} $
--   handle
