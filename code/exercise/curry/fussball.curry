-- Wählt nichtdeterministisch ein Element einer Liste aus
listQ :: a -> [a] -> a
listQ = foldl (?)

-- Mengen der vorgegebenen Paare
spieltFuerS = listQ ["vanveenendaal", "ned"] [["gayle", "can"],["akaffou", "civ"], ["mykjaland", "nor"],["mittag", "ger"], ["angerer", "ger"], ["henry","fra"], ["espinoza", "mex"]]

spieltInS = listQ ["can", "gruppeA"] [["ned", "gruppeA"], ["ger", "gruppeB"], ["civ", "gruppeB"], ["mex", "gruppeF"], ["fra", "gruppeF"], ["nor", "gruppeB"]]

vorrundenGegnerS = listQ ["ger", "nor"] [["nor", "ger"], ["ger", "civ"], ["civ", "ger"], ["nor", "civ"], ["civ", "nor"], ["can", "ned"], ["ned", "can"],["fra", "mex"], ["mex", "fra"]]

-- Definition der Prädikate 
spieltFuer s l = [s,l] =:= spieltFuerS 

spieltIn l g = [l,g] =:= spieltInS

vorrundenGegner l1 l2 = [l1, l2] =:= vorrundenGegnerS

-- Kombination der Prädikate mit freien Variablen
spieltInGruppe s g = spieltFuer s l & spieltIn l g where l free

spieltGegen s1 s2 = spieltFuer s1 l1 & spieltFuer s2 l2 & vorrundenGegner l1 l2 where l1,l2 free 
