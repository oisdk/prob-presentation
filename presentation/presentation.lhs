\documentclass[usenames,dvipsnames]{beamer}
\usepackage{xcolor}
\usepackage{amsmath}
% \setbeameroption{show notes}
\usetheme{metropolis}

%include polycode.fmt

%subst keyword a = "\textcolor{BlueViolet}{\textbf{" a "}}"
%format frac (a) (b) = "\frac{" a "}{" b "}"
%format * = "\times"

\newcommand{\id}[1]{\textsf{\textsl{#1}}}
\renewcommand{\Varid}[1]{\textcolor{Sepia}{\id{#1}}}
\renewcommand{\Conid}[1]{\textcolor{OliveGreen}{\id{#1}}}
\usepackage{listings}
\usepackage{biblatex}
\bibliography{../Probability.bib}
\title{Probabilistic Functional Programming}
\author{Donnacha Oisín Kidney}
\begin{document}
\frame{\titlepage}
\frame{\tableofcontents}
\section{Modeling Probability}
\begin{frame}
  How do we model stochastic and probabilistic processes in programming
  languages?
\end{frame}
\subsection{An Example}
\begin{frame}
  \frametitle{The Boy-Girl Paradox}
  \begin{enumerate}
    \item Mr. Jones has two children. The older child is a girl. What is the
      probability that both children are girls?
    \item \label{mrsmith} Mr. Smith has two children. At least one of them is a
      boy. What is the probability that both children are boys?
  \end{enumerate}
  \pause
  Is the answer to \ref{mrsmith} $\frac{1}{3}$ or $\frac{1}{2}$?
  \note{Gardner originally wrote that the second question (perhaps surprisingly)
    has the answer 1/3. However, he later acknowledged the question was
    ambiguous, and agreed that certain interpretations could correctly conclude
    its answer was 1/2}
  \pause

  Part of the difficulty in the question is that it's ambiguous: can we use
  programming languages to lend some precision?
\end{frame}
\begin{frame}[fragile, allowframebreaks]
  \frametitle{An Ad-Hoc Solution}
  Using normal features built in to the language.
  \begin{lstlisting}[language=Python]
from random import randrange, choice

class Child:
    def __init__(self):
        self.gender = choice(("boy", "girl"))
        self.age = randrange(18)
  \end{lstlisting}
  \begin{lstlisting}[language=Python]
from operator import attrgetter

def mr_jones():
    child_1 = Child()
    child_2 = Child()
    eldest = max(child_1, child_2,
                 key=attrgetter('age'))
    assert eldest.gender == 'girl'
    return [child_1, child_2]
  \end{lstlisting}
  \begin{lstlisting}[language=Python]

def mr_smith():
    child_1 = Child()
    child_2 = Child()
    assert child_1.gender == 'boy' or \
           child_2.gender == 'boy'
    return [child_1, child_2]
  \end{lstlisting}
\end{frame}
\subsection{Unclear Semantics}
\begin{frame}[fragile]
  \frametitle{Unclear semantics}
  What contracts are guaranteed by probabilistic functions? What does it mean
  \emph{exactly} for a function to be probabilistic? Why isn't the
  following\footfullcite{munroe_xkcd_2007} ``random''?
  \begin{lstlisting}[language=c]
int getRandomNumber()
{
  return 4; // chosen by fair dice roll.
            // guaranteed to be random.
}
  \end{lstlisting} 
\end{frame}
\begin{frame}[fragile]
  What about this?
  \begin{lstlisting}[language=Python]
  children_1 = [Child(), Child()]
  children_2 = [Child()] * 2
  \end{lstlisting}
  How can we describe the difference between \verb+children_1+ and
  \verb+children_2+?
  \note{The first runs two random processes; the second only one. Both have the
    same types, both look like they do the same thing. We need a good way to
    describe the difference between them.}
\end{frame}
\subsection{Underpowered}
\begin{frame}[fragile]
  \frametitle{Underpowered}
  There are many more things we may want to do with probability distributions.

  What about expectations?
  \begin{lstlisting}[language=Python]
def expect(predicate, process, iterations=100):
    success, tot = 0, 0
    for _ in range(iterations):
        try:
            success += predicate(process())
            tot += 1
        except AssertionError:
            pass
    return success / tot
  \end{lstlisting}
  \note{This solution is both inefficient and inexact. Also, we may want to
    express other attributes of probability distributions: independence, for
    example.}
\end{frame}
\begin{frame}[fragile]
  \frametitle{The Ad-Hoc Solution}
  \begin{lstlisting}[language=Python]
expect(lambda children: all(child.gender == 'girl'
                            for child in children),
       mr_jones)
expect(lambda children: all(child.gender == 'boy'
                            for child in children),
       mr_smith)
  \end{lstlisting}
\end{frame}
\section{Monadic Modeling}
\begin{frame}
  \frametitle{A DSL}
  What we're approaching is a DSL, albeit an unspecified one.

  Three questions for this DSL:
  \begin{itemize}
    \item Why should we implement it? What is it useful for?
    \item How should we implement it? How can it be made efficient? 
    \item Can we glean any insights on the nature of probabilistic computations
      from the language? Are there any interesting symmetries?
  \end{itemize}
\end{frame}
\subsection{The Erwig And Kollmansberger Approach}
\begin{frame}[fragile]
  \frametitle{The Erwig And Kollmansberger Approach}
  First approach\footfullcite{erwig_functional_2006}:
  \begin{code}
newtype Dist a = Dist { runDist :: [(a, Rational)] }
  \end{code} 
  A distribution is a list of possible events, each tagged with a probability.
\end{frame}
\begin{frame}
  A random integer, then, is:
  \begin{code}
type RandInt = Dist Int
  \end{code}
  This lets us encode (in the types) the difference between:
\begin{code}
  children_1 :: [Dist Child]
  children_2 :: Dist [Child]
\end{code}
\end{frame}
\begin{frame}[fragile]
  As we will use this as a DSL, we need to define the language features we used
  above:
\begin{lstlisting}[language=Python]
def mr_smith():
    child_1 = Child()
    child_2 = Child()
    assert child_1.gender == 'boy' or \
           child_2.gender == 'boy'
    return [child_1, child_2]
\end{lstlisting}
  \begin{enumerate}
    \item \verb+=+ (assignment)
    \item \verb+assert+
    \item \verb+return+
  \end{enumerate}
\end{frame}
\begin{frame}
  \frametitle{Assignment}
  This is encapsulated by the ``monadic bind'':
  \begin{code}
(>>=) :: Dist a -> (a -> Dist b) -> Dist b
  \end{code}
  When we assign to a variable in a probabilistic computation, everything that
  comes later is conditional on the result of that assignment. We are therefore
  looking for the probability of the continuation given the left-hand-side; this
  is encapsulated by multiplication:
  \begin{code}
xs >>= f = Dist  [  (y, xp * yp)
                 |  (x, xp) <- runDist xs
                 ,  (y, yp) <- runDist (f x) ]
  \end{code}
\end{frame}
\begin{frame}
  \frametitle{Assertion}
  Assertion is a kind of conditioning: given a statement about an event, it
  either occurs or it doesn't.
\begin{code}
guard :: Bool -> Dist ()
guard True   = Dist [((), 1)]
guard False  = Dist []
\end{code}
\end{frame}
\begin{frame}
  \frametitle{Return}
  Return is the ``unit'' value for a distribution; the certain event, the
  unconditional distribution.
\begin{code}
  return :: a -> Dist a
  return x = Dist [(x, 1)]
\end{code}
\end{frame}
\begin{frame}
  \frametitle{Putting it all Together}
  \begin{code}
mrSmith :: Dist [Child]
mrSmith = do
  child1 <- child
  child2 <- child
  guard (gender child1 == Boy || gender child2 == Boy)
  return [child1, child2]

  
expect :: (a -> Rational) -> Dist a -> Rational
expect p xs = frac (sum [ p x * xp | (x,xp) <- runDist xs ]) (sum [ xp | (_,xp) <- runDist xs])
  \end{code} 
\end{frame}
\begin{frame}
  Theoretical Basis
  
\end{frame}
\end{document}

