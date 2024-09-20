module Inky

import Control.App
import Control.App.Console
import Control.App.FileIO
import Inky.Context
import Inky.Parser
import Inky.Term.Parser
import Inky.Type
import Inky.Type.Pretty
import System.File.ReadWrite
import System.File.Virtual
import Text.Lexer
import Text.PrettyPrint.Prettyprinter
import Text.PrettyPrint.Prettyprinter.Render.Terminal

%default partial

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

checkType : HasErr String es => Ty [<] () -> App es ()
checkType a = do
  let False = illFormed a
    | True => throw "type ill-formed"
  pure ()

printType :
  PrimIO es => {default defaultLayoutOptions opts : LayoutOptions} ->
  Ty [<] () -> App es ()
printType a = do
  primIO $ renderIO $ layoutSmart opts $ prettyType a Open

ppType : FileIO es => PrimIO es => HasErr String es => App es ()
ppType = do
  file <- fGetStr stdin
  toks <- lexInkyString file
  a <- parseType toks
  checkType a
  printType a

main : IO ()
main =
  run $
  handle {err = IOError}
    (handle {err = String} ppType
      (const $ pure ())
      printErrLn)
    (const $ pure ())
    (printErrLn . show)
  where
  printErrLn : PrimIO es => String -> App es ()
  printErrLn msg = do
    primIO $ () <$ fPutStrLn stderr msg
    pure ()
