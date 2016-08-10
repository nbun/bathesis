curroqc :: String -> String
curroqc s = curroq s 0 0

curroq :: String -> Int -> Int -> String
curroq []      _  _  = []
curroq s@(c : r) cr cb = case c of
                         '(' -> c : (curroq r (cr + 1) cb)
                         ')' -> c : (curroq r (cr - 1) cb)
                         '[' -> c : (curroq r 0  (cb + 1))
                         ']' -> c : (curroq r cr (cb - 1))
                         ',' | cr == 0   -> ';': (curroq r cr cb)
                             | otherwise ->  c : (curroq r cr cb)
                         'T' | (isPrefixOf "Type" s) -> "Typec" ++ (curroq (drop 4 s)  cr cb)
                             | otherwise ->  c : (curroq r cr cb)
                         _   -> c : (curroq r cr cb)

isPrefixOf :: [a] -> [a] -> Bool
isPrefixOf []    _  = True 
isPrefixOf (x:_) [] = False
isPrefixOf (x:xs) (y:ys) =  x == y && isPrefixOf xs ys
