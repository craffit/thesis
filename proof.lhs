%include proof.fmt

\subsection{Inference rule properties}
What is left is to proof that the property is preserved by all derivation rules. Of course, this assumes that
the user has supplied a transformation which adheres to the required properties.

\subsubsection{Var rule}

\begin{center}
\inferrule{|x `rw` x' : F `elem` G|}
          {|G +- x `rwe` x' : F|}
\end{center}

We have to proof |dimap_F G rep abs x' == x|

>  dimap_F G rep abs x'
>== {|x `rw` x' : F `elem` G|}
>  dimap_F (Gx, x `rw` x' : F_a) rep abs x'
>== { Definition dimap_F G }
>  dimap_F rep abs x' @ mkSub (Gx, x `rw` x' : F_a)
>== { Definition mkSub }
>  dimap_F rep abs x' @ [x'/dimap_F abs rep x] `comp` mkSub Gx
>== { Apply substitution }
>  dimap_F rep abs x' @ [x'/dimap_F abs rep x] `comp` mkSub Gx
>== { Definition mkSub }
>  dimap_F rep abs (dimap_F abs rep x) @ mkSub Gx
>== { No eligible substitution in Gx }
>  dimap_F rep abs (dimap_F abs rep x)
>== { Functor composition }
>  dimap_F (abs `comp` rep) (abs `comp` rep) x
>== { Retraction identity }
>  dimap_F id id x
>== { Functor identity }
>  x

\subsubsection{Abstraction rule}

\begin{center}
\inferrule{|Gx; x `rw` x : F_a +- e `rwe` e' : F_r|}
          {|G +- \x. e `rwe` \x. e' : F_a -> F_r|}
\end{center}

We have to proof the following equivalence:

> (dimap(F_a -> F_r)) G rep abs (\x. e') == \x. e

From the premises we know that:

> dimap_Fr (Gx, x `rw` x : F_a) rep abs e' == e

Proof:

>  (dimap(F_a -> F_r)) G rep abs (\x. e')
>== { Definition (dimap(F_a -> F_r)) G }
>  (dimap(F_a -> F_r)) rep abs (\x. e') @ mkSub G
>== { Commute substitution over lambda }
>  (dimap(F_a -> F_r)) rep abs (\x. e' @ mkSub Gx)
>== { Definition dimap }
>  dimap_Fr G rep abs `comp` (\x. e' @ mkSub Gx) `comp` dimap_Fa G abs rep
>== { Eta expansion }
>  (\x. dimap_Fr G rep abs `comp` (\x. e' @ mkSub Gx) `comp` dimap_Fa G abs rep $ x)
>== { Evaluation }
>  (\x. dimap_Fr rep abs (e' @ [x/dimap_Fa abs rep x] `comp` mkSub Gx)
>== { Definition mkSub }
>  (\x. dimap_Fr rep abs e' @ mkSub (Gx, x `rw` x : F_a))
>== { Definition dimap }
>  (\x. dimap_Fr (Gx, x `rw` x : F_a) rep abs e')
>== { Premisse }
>  (\x. e)

\subsubsection{Application rule}
\begin{center}
\inferrule{|G +- f `rwe` f' : F_a -> F_r | \\\\
           |G +- e `rwe` e' : F_a |}
          {|G +- f e `rwe` f' e' : F_r|}
\end{center}

We have to proof the following equality:

> dimap_Fr G rep abs (f' e') == f e

From the premises we know that:

> dimap_F G rep abs f'  == f
> dimap_Fa G rep abs e' == e

Proof:

>  dimap_Fr G rep abs (f' e')
>== { Definition dimap_Fr G }
>  dimap_Fr rep abs (f' e') @ mkSub G
>== { Property below }
>  dimap_F rep abs f' (dimap_FA rep abs e') @ mkSub G
>== { Distribute substitution }
>  dimap_F rep abs f' @ mkSub G (dimap_FA rep abs e' @ mkSub G)
>== { Definition dimap }
>  dimap_F G rep abs f' (dimap_FA G rep abs e')
>== { Induction hypotheses }
>  f e

Extra property |dimap_Fr rep abs (f' e') == (dimap(F_a -> F_r)) rep abs f' (dimap_Fa rep abs e')|

>  (dimap(F_a -> F_r)) rep abs f' (dimap_Fa rep abs e')
>== { Definition of dimap }
>  dimap_Fr rep abs $ f' $ dimap_Fa abs rep $ dimap_FA rep abs e'
>== { Functor composition }
>  dimap_FR rep abs $ f' $ dimap_Fa (rep `comp` abs) (rep `comp` abs) e'
>== { rep . abs :: i == id }
>  dimap_Fr rep abs $ f' $ dimap_Fa id id e'
>== { Functor identity }
>  dimap_Fr rep abs (f' e')

\subsubsection{Rep rule}
Applying rep to some source term results in a term which can be made equal to the source term
by applying abs to it. This is reflected in the reasoning below.

\begin{center}
\inferrule{|G +- e `rwe` e' : A|}
          {|G +- e `rwe` rep e' : Id|}
\end{center}

We need to proof that |dimap_Id G rep abs (rep e') == e|. From the premises we know
that |dimap_A G rep abs e' == e|.

>  dimap_Id G rep abs (rep e')
>== { Definition dimap_Id G }
>  dimap_Id rep abs (rep e') @ mkSub G
>== { Definition dimap_Id }
>  abs (rep e') @ mkSub G
>== { Retraction }
>  e' @ mkSub G
>== { Identity function }
>  id e' @ mkSub G
>== { Definition dimap_A  }
>  dimap_A rep abs e' @ mkSub G
>== { Definition dimap_A G }
>  dimap_A G rep abs e'
>== { Premisse }
>  e
 
\subsubsection{Abs rule}
Applying abs to a suitable term equalizes the result and source term.
          
\begin{center}
\inferrule{|G +- e `rwe` e' : Id|}
          {|G +- e `rwe` abs e' : A|}
\end{center}

We have to proof |dimap_A G rep abs (abs e') == e|. From the premises we know
that |dimap_Id G rep abs e' == e|.

>  dimap_A G rep abs (abs e')
>== { Definition dimap_A G }
>  dimap_A rep abs (abs e') @ mkSub G
>== { Definition dimap_A }
>  abs e' @ mkSub G
>== { Definition dimap_Id }
>  dimap_Id rep abs e' @ mkSub G
>== { Defintion dimap_Id G }
>  dimap_Id G rep abs e'
>== { Premise }
>  e

\subsubsection{Transform rule}

\begin{center}
\inferrule{|p1 `rw` p2 `elem` env|\\\\ 
           |G; D +- e `rwe` e' : F_1| \\\\
           |G; D `rwr` p1 `rw` p2 => e' : F_1 R `rw` e'' : F_2 R|
          }
          {|G; D `tr` e `rwe` e'' : F_2|}
\end{center}

From the |Rewrite| premise we get the assertions that

> F_1 A = F_2 A
> dimap_F1 rep abs sub_P(e) = dimap_F2 rep abs sub_P(e')

From this we can see that the type of e is still valid after transformation (|F_1 A == F_2 A|).
For the terms the proof also follows easily.

>  dimap_F2 rep abs sub_G(e'')
>= { Premisse `rwr` }
>  dimap_F1 rep abs sub_G(e')
>= { Premisse `tr` }
>  e

\subsubsection{Rewrite rule}

\begin{center}
\inferrule{|G; D `mat` p1 @ e1 : F_1 R => S| \\\\
           |G; D `app` S @ p2 => e2 : F_2 R| \\\\
           |F_1 A = F_2 A|
           }
           {|G; D `rwr` p1 `rw` p2 @ e1 : F_1 R => e2 : F_2 R|}
\end{center}

First We have to proof that |F_1 A = F_2 A|, this follows easily from the premises.

The second thing we have to show is that:

> dimap_F1 rep abs sub_P(e) = dimap_F2 rep abs sub_P(e')

We have restricted the user to only allow rewrite rules which abide the following law:

\begin{center}
\inferrule{|forall S, D, G| \and |P = mkSub(D)| \\\\
           |G; D `app` S @ p1 => e1 : F_1 R| \\\\
           |G; D `app` S @ p2 => e2 : F_2 R| \\\\
           |F_1 A == F_2 A| \\\\
           |->| \\\\
           |dimap_F1 rep abs sub_P(e1) = dimap_F2 rep abs sub_P(e2)|}
          {|p1 `rw` p2|}
\end{center}           

Thus is we can proof the entire top side of the implication, we know that the desired law holds. |F_1 A == F_2 A|
follows from the premises. |G; D `app` S @ p2 => e2 : F_2 R| also follows directly. 

To proof |G; D `app` S @ p1 => e1 : F_1 R|, we need the following lemma:

> G; D `mat` p1 @ e1 : F_1 R => S 
>    -> 
> G; D `app` S @ p1 => e1 : F_1 R

Eg. Mathing and then applying yields the same term. This is easy to see from the symmetric
nature of matching and applying of patterns.

We can proof the left side of this implication, so we have our proof for |G; D `app` S @ p1 => e1 : F_1 R|

