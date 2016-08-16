import System
import FlatCurry.Files
import FlatCurry.ShowCoq
import FlatCurry.Types
import GetOpt
import Maybe (fromMaybe)

showFlatCoq :: [Prelude.Char] -> Prelude.IO ()
showFlatCoq s = do 
  flatProg  <- readFlatCurry s
  let (Prog modname _ _ _ _) = flatProg
      flatProgS = (showFlatProgCoq flatProg)
      coqProg   = headerString ++ importString ++ defString modname ++ flatProgS ++ ['.','\n']
    in putStr coqProg

headerString = "(* This is an automatically generated Coq source file. It represents a\n" ++
               "   Curry program in modified flatCurry syntax and can be compiled by\n" ++
               "   generating a _CoqProject with '-c'. *)\n\n"

importString = "Require Import CQE.FlatCurry Lists.List.\n" ++
               "Import ListNotations.\n\n"

defString name = "Definition " ++ name ++ "_coq := "

coqProjectString name = "# Run 'coq_makefile -f _CoqProject -o Makefile' to generate a Makefile\n" ++
                        "-Q . CQE\n\n" ++ "FlatCurry.v\n" ++ name ++ "_coq.v\n"

showCoqProject :: [Prelude.Char] -> Prelude.IO ()
showCoqProject s = do
      flatProg  <- readFlatCurry s
      let (Prog modname _ _ _ _) = flatProg
       in putStr (coqProjectString modname)
      
main :: Prelude.IO ()
main = do
   args <- getArgs
   opts <- progOpts args
   if length (snd opts) /= 1 then ioError (userError "Please specify a .curry input file.") else return ()
   if elem CoqProject (fst opts) then showCoqProject (args!!1) else showFlatCoq (head args)
   
data Flag = CoqProject

options :: [OptDescr Flag]
options = [Option ['c'] ["coqproject"] (NoArg CoqProject) "generate _CoqProject file"]

progOpts :: [String] -> IO ([Flag], [String])
progOpts argv =
       case getOpt Permute options argv of
          (o,n,[]  ) -> return (o,n)
          (_,_,errs) -> ioError (userError (concat errs ++ usageInfo header options))
      where header = "Usage: showFlatCoq [OPTION...] file\nYou have to compile the .curry file first!"
