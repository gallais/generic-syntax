%include lhs2TeX.fmt

\begin{code}
{-# LANGUAGE GADTs, DataKinds, KindSignatures #-}

module LC where

\end{code}
%<*lc>
\begin{code}
data Term (a :: *) where
  V :: a -> Term a
  L :: Term (Maybe a) -> Term a
  A :: Term a -> Term a -> Term a
\end{code}
%</lc>
%<*fin>
\begin{code}
data Nat = Z | S Nat

data Fin (n :: Nat) where
  Here  :: Fin (S n)
  There :: Fin n -> Fin (S n)
\end{code}
%</fin>
%<*lcnat>
\begin{code}
data Term (n :: Nat) where
  V :: Fin n -> Term n
  L :: Term (S n) -> Term n
  A :: Term n -> Term n -> Term n
\end{code}
%</lcnat>

%<*lcfull>
\begin{code}
data Term (i :: Type) (g :: [Type]) where
  V :: In i g -> Term i g
  L :: Term t (s : g) -> Term (Arr s t) g
  A :: Term (Arr s t) g -> Term s g -> Term t g
\end{code}
%</lcfull>
