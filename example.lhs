\begin{figure}[t]
  \begin{prooftree}
    \def\extraVskip{4pt}
              \AxiomC{}
            \LeftLabel{Var}
            \UnaryInfC{|x : Id, empty +- x `rw` x : Id|}
                \AxiomC{}
              \LeftLabel{Id}
              \UnaryInfC{|empty +- "mies" `rw` "mies" : String|}
            \LeftLabel{Rep}
            \UnaryInfC{|x : Id, empty +- "mies" `rw` rep "mies" : Id|}
          \LeftLabel{Comp}
          \BinaryInfC{|x : Id, empty +- x ++ "mies" `rw` x `comp` rep "mies" : Id|}
        \LeftLabel{Abs}
        \UnaryInfC{|empty +- \x. x ++ "mies" `rw` \x. x `comp` rep "mies" : Id -> Id|}
            \AxiomC{}
          \LeftLabel{Id}
          \UnaryInfC{|empty +- "aap" `rw` "aap" : String|}
        \LeftLabel{Rep}
        \UnaryInfC{|empty +- "aap" `rw` rep "aap" : Id|}
      \LeftLabel{|App|}
      \BinaryInfC{|empty +- (\x. x ++ "mies") "aap" `rw` (\x. x `comp` rep "mies") (rep "aap") : Id|}
    \LeftLabel{Abs}
    \UnaryInfC{|empty +- (\x. x ++ "mies") "aap" `rw` abs $ (\x. x `comp` rep "mies") (rep "aap") : String|}
  \end{prooftree}
\end{figure}