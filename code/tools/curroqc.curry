curroqc :: String -> String
curroqc s = curroq s 0 0

curroq :: String -> Int -> Int -> String
curroq []      _  _  = []
curroq s       cr cb | s == "Type" ++ r = "Typec" ++ (curroq r cr cb) where r free
curroq (c : s) cr cb | c == '(' = c : (curroq s (cr + 1) cb)
                     | c == ')' = c : (curroq s (cr - 1) cb)
                     | c == '[' = c : (curroq s 0  (cb + 1))
                     | c == ']' = c : (curroq s cr (cb - 1))
                     | and [c == ',', cb > 0, cr == 0] = ';' : (curroq s cr cb)
                     | otherwise = c : (curroq s cr cb)
