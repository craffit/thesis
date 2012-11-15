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
                  \AxiomC{}
                \LeftLabel{|Tr-Con|}
                \UnaryInfC{|x : tyI , empty `stlc` "b" `rw` "b" : String|}
              \LeftLabel{|Tr-Rep|}
              \UnaryInfC{|x : tyI , empty `stlc` "b" `rw` rep "b" : tyI|}
            \LeftLabel{|Tr-App|}
            \BinaryInfC{|x : tyI , empty `stlc` x ++ "b" `rw` x `comp` rep "b" : tyI|}
          \LeftLabel{|Tr-Lam|}
          \UnaryInfC{|empty `stlc` \x. x ++ "b" `rw` \x. x `comp` rep "b" : tyI -> tyI|}
              \AxiomC{}
            \LeftLabel{|Tr-Con|}
            \UnaryInfC{|empty `stlc` "a" `rw` "a" : String|}
          \LeftLabel{|Tr-Rep|}
          \UnaryInfC{|empty `stlc` "a" `rw` rep "a" : tyI|}
        \LeftLabel{|Tr-App|}
        \BinaryInfC{|empty `stlc` (\x. x ++ "b") "a" `rw` (\x. x `comp` rep "b") (rep "a") : tyI|}
      \LeftLabel{|Tr-Abs|}
      \UnaryInfC{|empty `stlc` (\x. x ++ "b") "a" `rw` abs ((\x. x `comp` rep "b") (rep "a")) : String|}
    \end{prooftree}
  \caption{An example transformation derivation}
  \label{fig:hughesexample}
\end{sidewaysfigure}