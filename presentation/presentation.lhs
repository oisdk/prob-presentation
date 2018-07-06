\documentclass{beamer}
%include polycode.fmt
\usepackage{listings}
\usepackage{biblatex}
\bibliography{../Probability.bib}
\title{Probabilistic Functional Programming}
\author{Donnacha Oisín Kidney}
\begin{document}
\frame{\titlepage}
\begin{frame}
  How do we model stochastic and probabilistic processes in programming
  languages?
\end{frame}
\begin{frame}[fragile]
  The same way we model any other process: using the semantics and features
  built into the language.
  \begin{lstlisting}[language=Python]
from random import randrange

def roll_die():
  return randrange(1,7)
  \end{lstlisting}
\end{frame}
\begin{frame}[fragile]
  Problem: semantics are unclear.\footfullcite{munroe_xkcd_2007}

  \begin{lstlisting}[language=c]
int getRandomNumber()
{
  return 4; // chosen by fair dice roll.
            // guaranteed to be random.
}
  \end{lstlisting}
\end{frame}
\begin{frame}[fragile]
  \begin{lstlisting}[language=Python]
randomly_chosen = roll_die()

def roll_die_2():
    return randomly_chosen
  \end{lstlisting}

  What's the difference between \verb+roll_die+ and \verb+roll_die_2+?
\end{frame}
\begin{frame}[fragile,fragile]
  Problem: not as powerful as we'd like.
\begin{lstlisting}[language=Python]
def expect(predicate, process, iterations):
    success = sum(predicate(process())
                  for _ in range(iterations))
    return success / iterations

expect(lambda y: 5 == y, roll_die, 100)
0.17
\end{lstlisting}
\end{frame}
\begin{frame}
  Solution: design a DSL for probabilistic programs which solves the problems
  above.

  Three questions for this DSL:
  \begin{itemize}
    \item Why should we implement it? What is it useful for?
    \item How should we implement it? How can it be made efficient? 
    \item Can we glean any insights on the nature of probabilistic computations
      from the language? Are there any interesting symmetries?
  \end{itemize}
\end{frame}
\begin{frame}[fragile]
  The first approach\footfullcite{erwig_functional_2006} starts with a simple
  and elegant answer to the second question.

  We'll model a distribution as a list of events, with each possible event
  tagged with its probability.
  \begin{code}
newtype Dist a = Dist { runDist :: [(a, Rational)] }
  \end{code}
\end{frame}
\end{document}
