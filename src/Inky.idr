module Inky

import Control.App
import Control.App.Console
import Control.App.FileIO

import Data.DPair
import Data.String

import Flap.Decidable
import Flap.Decidable.Maybe
import Flap.Parser

import Inky.Term
import Inky.Term.Checks
import Inky.Term.Parser
import Inky.Term.Pretty
import Inky.Term.Pretty.Error
import Inky.Type.Pretty

import System
import System.File.Mode
import System.File.ReadWrite
import System.File.Virtual
import System.GetOpts

import Text.Lexer
import Text.PrettyPrint.Prettyprinter
import Text.PrettyPrint.Prettyprinter.Render.Terminal

%hide Flap.Data.SnocList.Thinning.(.)

FilePath : Type
FilePath = String

record Erased (a : Type) where
  constructor Forget
  0 value : a

record SynthFailed where
  constructor UhOh
  term : Term Bounds [<] [<]
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

partial
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

partial
readFileOrStdin : FileIO es => HasErr IOError es => Maybe FilePath -> App es String
readFileOrStdin Nothing = readFile stdin
readFileOrStdin (Just path) = withFile path Read throw readFile

lexInkyString : HasErr (WithBounds String) es => String -> App es (List (WithBounds InkyToken))
lexInkyString file = do
  let (tokens, _, _, "") = lex tokenMap file
    | (_, line, col, rest) =>
      throw (MkBounded "unexpected character" False (MkBounds line col line col))
  pure (filter (\x => relevant x.val.kind) tokens)

ParseErr : Type
ParseErr = ParseErr (WithBounds InkyError) InkyKind

doParse :
  (e : HasErr (List1 ParseErr) es) =>
  (p : InkyParser False [<] [<] a) ->
  {auto 0 wf : WellFormed ListSet p} ->
  List (WithBounds InkyToken) ->
  (s : state) ->
  App es (a s)
doParse p toks s =
  case (parse ListSet p).runParser s toks of
    Ok res [] _ => pure res
    Ok res (x :: _) _ => throw @{e} (Unexpected [] x ::: [])
    SoftErr errs _ _ => throw errs
    Err errs => throw errs

partial
parseType :
  Has
    [ HasErr (WithBounds String)
    , HasErr (List1 ParseErr)
    , HasErr Err
    , HasErr IOError
    , FileIO
    ] es =>
  Maybe FilePath -> App es (Ty [<])
parseType path = do
  txt <- readFileOrStdin path
  toks <- lexInkyString txt
  doParse OpenType toks [<]

partial
parseTerm :
  Has
    [ HasErr (WithBounds String)
    , HasErr (List1 ParseErr)
    , HasErr Err
    , HasErr IOError
    , FileIO
    ] es =>
  (termPath, tyPath : Maybe FilePath) ->
  App es (Term Bounds [<] [<])
parseTerm termPath tyPath = do
  txt <- readFileOrStdin termPath
  toks <- lexInkyString txt
  t <- doParse OpenTerm toks ([<], [<])
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
  (t : Term Bounds [<] [<]) ->
  HasErr SynthFailed es =>
  App es (Subset (Ty [<]) (Synths [<] [<] t))
synthTerm t = do
  let Just a `Because` prf = synths [<] [<] t
    | Nothing `Because` contra => throw (UhOh t contra)
  pure (Element a prf)

writeFile : FileIO es => File -> SimpleDocStream Void -> App es ()
writeFile file SEmpty = pure ()
writeFile file (SChar c rest) = do fPutStr file (pack [c]); writeFile file rest
writeFile file (SText len text rest) = do fPutStr file text; writeFile file rest
writeFile file (SLine i rest) = do fPutStr file (strCons '\n' $ textSpaces i); writeFile file rest
writeFile file (SAnnPop rest) = writeFile file rest

openFile : FileIO es => Maybe String -> (File -> App es a) -> App es a
openFile Nothing cont = cont stdout
openFile (Just path) cont = withFile path WriteTruncate throw cont

printTerm :
  FileIO es => (opts : LayoutOptions) ->
  Term m [<] [<] ->
  (output : Maybe String) ->
  App es ()
printTerm opts a out =
  openFile out $ \file =>
    writeFile file $ layoutSmart opts $ prettyTerm a Open

-- Arguments -------------------------------------------------------------------

record GlobalOptions where
  constructor MkGlobalOptions
  help: Bool
  version: Bool

defaultGlobalOptions : GlobalOptions
defaultGlobalOptions = MkGlobalOptions False False

setHelp : GlobalOptions -> GlobalOptions
setHelp = { help := True }

setVersion : GlobalOptions -> GlobalOptions
setVersion = { version := True }

record FormatOptions where
  constructor MkFormatOptions
  global: GlobalOptions
  width: Maybe Nat
  output: Maybe FilePath

defaultFormatOptions : FormatOptions
defaultFormatOptions = MkFormatOptions
  { global = defaultGlobalOptions
  , width = Nothing
  , output = Nothing
  }

record CheckOptions where
  constructor MkCheckOptions
  global: GlobalOptions
  type: Maybe FilePath

defaultCheckOptions : CheckOptions
defaultCheckOptions = MkCheckOptions
  { global = defaultGlobalOptions
  , type = Nothing
  }

globalOptions : List (OptDescr (GlobalOptions -> GlobalOptions))
globalOptions =
  [ MkOpt ['h'] ["help"]
    (NoArg $ the (GlobalOptions -> GlobalOptions) setHelp)
    "display this help and exit"
  , MkOpt ['v'] ["version"]
    (NoArg $ the (GlobalOptions -> GlobalOptions) setVersion)
    "display version information and exit"
  ]

formatOptions : List (OptDescr (FormatOptions -> FormatOptions))
formatOptions =
  [ MkOpt ['h'] ["help"]
    (NoArg $ the (FormatOptions -> FormatOptions) { global $= setHelp })
    "display this help and exit"
  , MkOpt ['v'] ["version"]
    (NoArg $ the (FormatOptions -> FormatOptions) { global $= setVersion })
    "display version information and exit"
  , MkOpt [] ["width"]
    (ReqArg' (\width =>
        if all isDigit (unpack width) then
          Right ({ width := Just (stringToNatOrZ width) })
        else
          Left "width must be an integer")
      "WIDTH")
    "set maximum width of lines to WIDTH"
  , MkOpt ['o'] ["output"]
    (ReqArg (\path => the (FormatOptions -> FormatOptions) { output := Just path }) "FILE")
    "output to FILE"
  ]

checkOptions : List (OptDescr (CheckOptions -> CheckOptions))
checkOptions =
  [ MkOpt ['h'] ["help"]
    (NoArg $ the (CheckOptions -> CheckOptions) { global $= setHelp })
    "display this help and exit"
  , MkOpt ['v'] ["version"]
    (NoArg $ the (CheckOptions -> CheckOptions) { global $= setVersion })
    "display version information and exit"
  , MkOpt [] ["type"]
    (ReqArg (\path => the (CheckOptions -> CheckOptions) { type := Just path }) "FILE")
    "type check according to type in FILE"
  ]

-- Driver ----------------------------------------------------------------------

data ProgramMode = Global | Format | Check

Show ProgramMode where
  show Global = ""
  show Format = "format"
  show Check = "check"

ModeOptionTy : ProgramMode -> Type
ModeOptionTy Global = GlobalOptions
ModeOptionTy Format = FormatOptions
ModeOptionTy Check = CheckOptions

synopsis : ProgramMode -> String
synopsis Global = "Manipulate and type check Artyst terms."
synopsis Format = "Format Artyst terms."
synopsis Check = "Type check Artyst terms."

getGlobal : (mode : ProgramMode) -> ModeOptionTy mode -> GlobalOptions
getGlobal Global = id
getGlobal Format = (.global)
getGlobal Check = (.global)

defaultOptions : (mode : ProgramMode) -> ModeOptionTy mode
defaultOptions Global = defaultGlobalOptions
defaultOptions Format = defaultFormatOptions
defaultOptions Check = defaultCheckOptions

modeOptions : (mode : ProgramMode) -> List (OptDescr (ModeOptionTy mode -> ModeOptionTy mode))
modeOptions Global = globalOptions
modeOptions Format = formatOptions
modeOptions Check = checkOptions

data OptErr
  = Errors (List1 String)
  | Unrecognised (List1 String)
  | ArgCount
  | Help ProgramMode
  | Version

0 Errs : List Error
Errs =
  [ SynthFailed
  , IOError
  , WithBounds String
  , List1 ParseErr
  , List1 (WithBounds String)
  , String
  , List String
  , OptErr
  , AppHasIO
  ]

getPath : HasErr OptErr es => List String -> App es (Maybe String)
getPath [] = pure Nothing
getPath [path] = pure (Just path)
getPath path = throw ArgCount

handleGlobal : HasErr OptErr es => ProgramMode -> GlobalOptions -> App es ()
handleGlobal mode global =
  if global.help then
     throw (Help mode)
  else if global.version then
     throw Version
  else
     pure ()

processResult :
  HasErr OptErr es =>
  (mode : ProgramMode) -> Result (ModeOptionTy mode -> ModeOptionTy mode) ->
  App es (ModeOptionTy mode, List String)
processResult mode result = do
  let [] = result.errors
    | (err :: errs) => throw (Errors (err ::: errs))
  let [] = result.unrecognized
    | (err :: errs) => throw (Unrecognised (err ::: errs))
  let opts = foldr (.) (\x => x) result.options (defaultOptions mode)
  handleGlobal mode (getGlobal mode opts)
  pure (opts, result.nonOptions)

partial
processFormat : FormatOptions -> Maybe String -> App Errs ()
processFormat opts path = do
  t <- parseTerm path Nothing
  let layoutOpts = mkLayoutOpts opts
  printTerm layoutOpts t opts.output
  where
  mkLayoutOpts : FormatOptions -> LayoutOptions
  mkLayoutOpts opts =
    let
      setWidth : LayoutOptions -> LayoutOptions
      setWidth =
        maybe id
          (\w => the (LayoutOptions -> LayoutOptions) { layoutPageWidth := AvailablePerLine (cast w) 1 })
          opts.width
    in
    setWidth defaultLayoutOptions

partial
processCheck : CheckOptions -> Maybe String -> App Errs ()
processCheck opts path = do
  t <- parseTerm path opts.type
  ignore (synthTerm t)

partial
Commands : List (String, (mode ** (ModeOptionTy mode -> Maybe String -> App Errs ())))
Commands =
  [ (show Format, (Format ** processFormat))
  , (show Check, (Check ** processCheck))
  ]

partial
processGlobal : List String -> App Errs ()
processGlobal args = do
  let result = getOpt RequireOrder globalOptions args
  (opts, args) <- processResult Global result
  case args of
    [] => throw (Help Global)
    (cmd :: args) => case lookup cmd Commands of
      Nothing => throw (Unrecognised (cmd ::: []))
      Just (mode ** f) => do
        let result = getOpt Permute (modeOptions mode) args
        (opts, args) <- processResult mode result
        path <- getPath args
        f opts path

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

Interpolation (List InkyKind) where
  interpolate [] = "end of input"
  interpolate [t] = interpolate t
  interpolate ts = "one of " ++ joinBy ", " (map interpolate ts)

partial
handleAllErrs : Maybe String -> App Errs () -> App [AppHasIO] ()
handleAllErrs arg0 =
  handleErr OptErr handleOptErr .
  handleErr (List String) (\msgs => do
      foldlM (\_, msg => primIO $ () <$ fPutStrLn stderr msg) () msgs
      primIO exitFailure) .
  handleErr String (throw . List.singleton) .
  handleErr (List1 $ WithBounds String) (throw . map interpolate . forget) .
  handleErr (List1 ParseErr) (throw . map errToString . forget) .
  handleErr (WithBounds String) (throw . (::: [])) .
  handleErr IOError (throw . show) .
  handleErr SynthFailed (\err => do
      printSynthFailed err
      primIO exitFailure)
  where
  errToString : ParseErr -> String
  errToString (BadEOF expected) = "expected \{expected}, got end of input"
  errToString (Unexpected expected got) =
    interpolate ("expected \{expected}, got \{got.val.kind}" <$ got)
  errToString (MapFail e) =
    let
      msg =
        case e.val of
          (UnboundTyVar str ctx) => "unbound type variable '\{str}'"
          (UnboundTmVar str ctx) => "unbound term variable '\{str}'"
          (DuplicateLabel str labels) => "repeated label '\{str}'"
    in interpolate (msg <$ e)

  partial
  handleOptErr : OptErr -> App [AppHasIO] a
  handleOptErr (Errors errs) = do
    traverse_ (primIO . ignore . fPutStrLn stderr) errs
    primIO exitFailure
  handleOptErr (Unrecognised errs) = do
    traverse_ (primIO . ignore . fPutStrLn stderr . ("unrecognised option " ++)) errs
    primIO exitFailure
  handleOptErr ArgCount = do
    primIO $ ignore $ fPutStrLn stderr "too many arguments"
    primIO exitFailure
  handleOptErr (Help Global) = do
    putStr """
    Usage: \{maybe "artyst" (last . split (== '/')) arg0} [COMMAND]
    \{synopsis Global}
      format   \{synopsis Format}
      check    \{synopsis Check}
    """
    primIO exitSuccess
  handleOptErr (Help mode) = do
    putStr $ flip usageInfo (modeOptions mode) """
    Usage: \{maybe "artyst" (last . split (== '/')) arg0} \{show mode} [OPTIONS]... [FILE]
    \{synopsis mode}
    """
    primIO exitSuccess
  handleOptErr Version = do
    putStrLn "artyst (Artyst) 0.1.0"
    primIO exitSuccess

partial
main : IO ()
main = run {l = MayThrow} $ do
  (cmd :: args) <- primIO getArgs
    | [] => handleAllErrs Nothing (throw $ Help Global)
  handleAllErrs (Just cmd) (processGlobal args)
