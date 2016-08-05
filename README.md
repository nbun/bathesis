# Formalisierung von Aussagen und Beweise über Curry-Programme in Coq

Im Rahmen dieser Bachelorarbeit soll erarbeitet und evaluiert werden, ob mit Hilfe von Coq die
Modellierung der Programmiersprache Curry in zufriedenstellender Weise
erfolgen kann. Curry [0] ist eine funktional-logische Sprache, die
die funktionalen Konzepte von Haskell(98, aber ohne Typklassen)
aufweist und diese mit Konzepten aus der Logik, wie Nichtdeterminismus
und freie Variablen, vereint.

[0] http://www-ps.informatik.uni-kiel.de/currywiki/  

## 1. Phase: Setup

* Aufsetzen eines funktionierenden Curry-Systems (KiCS2) [1][2]
* Aufsetzen einer funktionierenden Installation von Coq (IDE auch über
Linux möglich?) [2]
* Account-Erstellung für Institut-Git (nach erstmaligen Login über deinen
  stu-Account bzw. dein Informatikkürzel ist der Account automatisch
  freigeschaltet) [3]
 
[1] http://www-ps.informatik.uni-kiel.de/kics2/download.html  
[2] http://www-ps.informatik.uni-kiel.de/smap/smap.cgi?new/curry
(online Version zur Codeausführung)  
[3] https://coq.inria.fr/download  
[4] https://git.informatik.uni-kiel.de  

## 2. Phase: Einlesen in Programmiersprachen

* erste Programme in Curry mit Nichtdeterminismus schreiben (Wie
  wirken sich überlappende Pattern aus? Verwendung von `?` als
  Programmiertechnik; Quellen der Inspiration könnten die
  Prolog-Programme aus FortProg sein)
* Grundlagen von Coq erarbeiten (Quellen 5 und 6)

Quellen  
[5] http://www.cis.upenn.edu/~bcpierce/sf/current/toc.html (Kapitel 1 - 6)  
[6] http://osa1.net/posts/2014-07-12-fun-coq-exercises.html  

## 3. Phase: Anlesen der Repräsentation von Curry-Programmen und Repräsentation dieser in Coq

Curry-Programme werden in den gängigen Compilern in eine simplere
  (flache) Zwischensprache namens Flatcurry transformiert, die als
  Grundlage der meisten Aussagen über bzw. Transformationen von
  Curry-Programmen dient.

* Recherche zur Darstellung von FlatCurry
* Recherche zur Transformation von Curry-Programmen in
FlatCurry-Programme
* Implementierung der benötigten Datenstruktur in Coq

[7]
https://www.informatik.uni-kiel.de/~mh/papers/GanzingerFestschrift.pdf
(Kapitel 2, gerne das ganze Kapitel, am wichtigsten ist aber 2.5)  
[8]
http://www-ps.informatik.uni-kiel.de/kics2/lib/FlatCurry.Types.html
(Implementierung von FlatCurry in Curry)  
[9] https://www-ps.informatik.uni-kiel.de/kics2/Manual.pdf (Abstract
A1)  

## 4. Phase: Formalisierung der Typung von CuMin-Programmen in Coq

* Einarbeitung in Thematik durch Lesen des entsprechenden Kapitels in
"Software Foundations"

[10] http://www.cis.upenn.edu/~bcpierce/sf/current/Imp.html (Ähnliche
Vorgehensweise wie angestrebt, nur anhand einer fiktiven imperativen
Sprache "Imp")  
[11] http://www.cis.upenn.edu/~bcpierce/sf/current/toc.html (Kapitel
7 - 9 können als Vorbereitung zu dem obigen Link gelesen werden)  
[12] http://www.janis-voigtlaender.eu/MSSV14.html (CuMin + Typregeln)  
[13] http://www.cis.upenn.edu/~bcpierce/sf/current/Stlc.html#lab568 (Typregeln für "STLC") 

## 5. Phase: Erstmal etwas schreiben

* erste Stichpunkte und Ausformulierung zu Coq
* Latex-Vorlage [16] und Code-Highlighting [14][15]

[14] https://de.sharelatex.com/learn/Code_Highlighting_with_minted  
[15] http://pygments.org/languages/  
[16] https://www.informatik.uni-kiel.de/~mh/lehre/seminare/hinweise.html  

## 6. Phase: Formalisierung der Typung von FlatCurry

* analog zu CuMin soll nun die Typung von FlatCurry umgesetzt werden [17]
*  in der Umgebung soll nun jeder Konstruktor mit seinem (vollen) Typ als auch den Typvariablen (des übergeordneten Datentyps) abgelegt werden.  
   Beispiel:
   `data Either a b = Left a | Right b`
   `{ Left |-> (a -> Either a b, [a,b]), Right |> (b -> Either a b, [a,b]) }`
   Im Falle von Datentypdeklarationen findest du diese Information relativ direkt wieder:
     *"data type definition of the form*
 
        data t x1...xn = ...| c t1....tkc |…
        
     *is represented by the FlatCurry term*

       (Type t [i1,...,in] [...(Cons c kc [t1,...,tkc])…])

     *where each ij is the index of the type variable xj."*  
   Da die Typsubstitution Variablen als erstes Argument erhält, sollten direkt die Indizes abgelegt werden.

* ähnlich sollen auf Funktionen in der Umgebung abgelegt werden: neben der Typsignatur soll auch eine Liste mit den Typvariablen (bzw. Indizes) aus der Typsignatur hinterlegt sein. Leider musst du die aus der Signatur extrahieren, da wir hier eben keine explizit allquantifizierten Variablen haben wie in CuMin.
  Beispiel: `{ test |-> (a -> b -> Int -> Bool -> c, [a,b,c]) }`

[17] [FlatCurry Typing Rules](text/FlatCurryTyping.tex)