import System   
import FlatCurry.Files
import FlatCurry.Show

makeFlat :: [Prelude.Char] -> Prelude.IO ()
makeFlat s = do 
   flatProg <- (readFlatCurry s)
   putStr (showFlatProg flatProg)

first :: [a] -> a
first (l:_) = l

main :: Prelude.IO ()
main = do
   args <- getArgs
   makeFlat (first args)
