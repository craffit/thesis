\begin{sidewaysfigure}[t]
    \begin{prooftree}
      \def\extraVskip{4pt}
                              \AxiomC{}
                            \LeftLabel{|Tr-Comp|}
                            \UnaryInfC{|x : tyI , empty `stlc` (++) `rw` (`comp`) : tyI -> tyI -> tyI|}            
                              \AxiomC{}
                            \LeftLabel{|Tr-Var|}
                            \UnaryInfC{|x : tyI , empty `stlc` x `rw` x : tyI|}
                          \LeftLabel{|Tr-App|}
                          \BinaryInfC{|x : tyI , empty `stlc` (++) x `rw` (`comp`) x : tyI|}  
                        \noLine
                        \UnaryInfC{.}  
                      \noLine
                      \UnaryInfC{.}  
                    \noLine
                    \UnaryInfC{|x : tyI , empty `stlc` (++) x `rw` (`comp`) x : tyI|}  
                        \AxiomC{}
                      \LeftLabel{|Tr-Con|}
                      \UnaryInfI{|x : tyI , empty `stlc` "b"|\ }{|`rw` "b" : String|}
                    \LeftLabel{|Tr-Rep|}
                    \UnaryInfI{|x : tyI , empty `stlc` "b"|\ }{|`rw` rep "b" : tyI|}
                  \LeftLabel{|Tr-App|}
                  \insertBetweenHyps{\hskip -80pt}
                  \BinaryInfI{|x : tyI , empty `stlc` x ++ "b"|\ }{|`rw` x `comp` rep "b" : tyI|}
                \LeftLabel{|Tr-Lam|}
              \UnaryInfI{|empty `stlc` \x. x ++ "b"|\ }{|`rw` \x. x `comp` rep "b" : tyI -> tyI|}
            \noLine
            \UnaryInfC{.}  
          \noLine
          \UnaryInfC{.}  
        \noLine
        \UnaryInfI{|empty `stlc` \x. x ++ "b"|\ }{|`rw` \x. x `comp` rep "b" : tyI -> tyI|}  
              \AxiomC{}
            \LeftLabel{|Tr-Con|}
            \UnaryInfI{|empty `stlc` "a"|\ }{|`rw` "a" : String|}
          \LeftLabel{|Tr-Rep|}
          \UnaryInfI{|empty `stlc` "a"|\ }{|`rw` rep "a" : tyI|}
        \LeftLabel{|Tr-App|}
        \insertBetweenHyps{\hskip -30pt}
        \BinaryInfI{|empty `stlc` (\x. x ++ "b") "a"|\ }{| `rw` (\x. x `comp` rep "b") (rep "a") : tyI|}
      \LeftLabel{|Tr-Abs|}
      \UnaryInfI{|empty `stlc` (\x. x ++ "b") "a" |\ }{| `rw` abs ((\x. x `comp` rep "b") (rep "a")) : String|}
    \end{prooftree}
  \caption{An example transformation derivation}
  \label{fig:hughesexample}
\end{sidewaysfigure}