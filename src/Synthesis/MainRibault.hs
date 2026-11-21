{-# LANGUAGE LambdaCase #-}

module Main where

import System.Environment  (getArgs, getExecutablePath, lookupEnv)
import System.IO           (hPutStrLn, stderr)
import System.Exit         (exitFailure, exitWith, ExitCode(..))
import System.FilePath     (takeBaseName, takeDirectory, (</>))
import System.Directory    (createDirectoryIfMissing, makeAbsolute)
import System.Process      (rawSystem)
import GHC.Conc            (getNumProcessors)

import qualified Data.Text.Lazy    as TL
import qualified Data.Text.Lazy.IO as TLIO

import Analysis.Lexer     (scanAll)
import Analysis.Parser    (parse)
import Syntax             (Program)
import Analysis.Semantic  (checkAll)

import qualified Synthesis.Builder as DF
import qualified Synthesis.Codegen as CG

main :: IO ()
main = do
  (nPEs, file, appArgs) <- parseCliArgs

  exePath <- getExecutablePath
  let repoRoot = takeDirectory exePath
      baseName = takeBaseName file
      buildDir = "build" </> baseName

  createDirectoryIfMissing True buildDir
  talmDir <- maybe (repoRoot </> "TALM") id <$> lookupEnv "TALM_DIR"

  -- 1. Codegen: .hss → .fl
  src <- readFile file
  tokens <- case scanAll src of
    Left  err -> die' ("Lexical error: " ++ err)
    Right ts  -> pure ts
  let ast = parse tokens
  case checkAll ast of
    []   -> pure ()
    errs -> mapM_ (hPutStrLn stderr . show) errs >> exitFailure
  let flText = TL.fromStrict (CG.assemble (DF.buildProgram ast))
      flFile = buildDir </> (baseName ++ ".fl")
  TLIO.writeFile flFile flText
  info (file ++ " -> " ++ flFile)

  -- 2. Supers: generate and compile libsupers.so
  let supersHs = buildDir </> "Supers.hs"
  run "build_supers" "bash"
    [ repoRoot </> "tools" </> "build_supers.sh"
    , file
    , supersHs
    ]

  -- 3. FlowASM: .fl → .flb + .pla
  run "flowasm" "python3"
    [ talmDir </> "asm" </> "assembler.py"
    , "-n", show nPEs
    , flFile
    , "-o", buildDir </> baseName
    ]

  -- 4. Placement: spread instructions over the PEs (see 'placePEs').
  let plaFile = buildDir </> (baseName ++ ".pla")
  pes <- placePEs nPEs plaFile

  -- 5. Trebuchet: run
  let interp = talmDir </> "interp" </> "interp"
  absLib <- makeAbsolute (buildDir </> "libsupers.so")
  ec <- rawSystem interp $
    [ show pes
    , buildDir </> (baseName ++ ".flb")
    , buildDir </> (baseName ++ ".pla")
    , absLib
    ] ++ appArgs
  exitWith ec

-- ----------------------------------------------------------------
-- CLI
-- ----------------------------------------------------------------
parseCliArgs :: IO (Int, FilePath, [String])
parseCliArgs = getArgs >>= go Nothing Nothing
  where
    go mpes mfile ("--" : rest) = finish mpes mfile rest
    go mpes mfile ("-n" : n : rest) = go (Just (read n)) mfile rest
    go mpes Nothing (f : rest)
      | take 1 f /= "-" = go mpes (Just f) rest
    go mpes mfile [] = finish mpes mfile []
    go _ _ _ = usage

    finish _    Nothing  _       = usage
    finish mpes (Just f) appArgs = do
      n <- maybe getNumProcessors pure mpes
      pure (n, f, appArgs)

    usage = do
      hPutStrLn stderr "Usage: ribault [-n <PEs>] <program.hss> [-- app-args...]"
      exitFailure

-- ----------------------------------------------------------------
-- Placement
-- ----------------------------------------------------------------

-- | Instructions one Trebuchet PE can hold: interp.h declares
-- @instr_t instrs[MAX_INSTRS]@ per PE with @MAX_INSTRS 500@.
maxInstrsPerPE :: Int
maxInstrsPerPE = 500

-- | Rewrite the FlowASM placement file (first line = instruction count, then
-- one PE id per instruction) so instructions are split into contiguous
-- blocks over the PEs. FlowASM alone puts everything on PE 0. If the program
-- does not fit in the requested PEs, the PE count is raised to the minimum
-- that fits. Returns the PE count to run with.
placePEs :: Int -> FilePath -> IO Int
placePEs nPEs plaFile = do
  txt <- readFile plaFile
  let n = case lines txt of
            (h:_) | [(k, "")] <- reads h -> k
            _ -> 0 :: Int
      needed = (n + maxInstrsPerPE - 1) `div` maxInstrsPerPE
      pes    = maximum [1, nPEs, needed]
      per    = max 1 ((n + pes - 1) `div` pes)
  length txt `seq` pure ()
  if pes > nPEs
    then info ("program has " ++ show n ++ " instructions; raising PEs from "
               ++ show nPEs ++ " to " ++ show pes
               ++ " (Trebuchet holds " ++ show maxInstrsPerPE ++ " per PE)")
    else pure ()
  writeFile plaFile (unlines (show n : [ show (i `div` per) | i <- [0 .. n - 1] ]))
  pure pes

-- ----------------------------------------------------------------
-- Helpers
-- ----------------------------------------------------------------
run :: String -> String -> [String] -> IO ()
run label cmd args = do
  ec <- rawSystem cmd args
  case ec of
    ExitSuccess   -> pure ()
    ExitFailure n -> die' (label ++ " failed (exit " ++ show n ++ ")")

die' :: String -> IO a
die' msg = hPutStrLn stderr ("[ribault] ERROR: " ++ msg) >> exitFailure

info :: String -> IO ()
info msg = hPutStrLn stderr ("[ribault] " ++ msg)
