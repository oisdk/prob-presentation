\documentclass[usenames,dvipsnames]{beamer}
\usepackage{xcolor}
\usepackage{amsmath}
\usepackage{forest}
\usepackage{mathtools}
% \setbeameroption{show notes}
\usetheme{metropolis}

%include polycode.fmt

%subst keyword a = "\textcolor{BlueViolet}{\textbf{" a "}}"
%format frac (a) (b) = "\frac{" a "}{" b "}"
%format * = "\times"
%format Double = "\mathbb{R}"

\newcommand{\id}[1]{\textsf{\textsl{#1}}}
\renewcommand{\Varid}[1]{\textcolor{Sepia}{\id{#1}}}
\renewcommand{\Conid}[1]{\textcolor{OliveGreen}{\id{#1}}}
\usepackage{listings}
\usepackage{biblatex}
\usepackage{multicol}
\bibliography{../Probability.bib}
\title{Probabilistic Functional Programming}
\author{Donnacha Oisín Kidney}
\begin{document}
\frame{\titlepage}
\begin{frame}
  \begin{multicols}{2}
    \tableofcontents
  \end{multicols}
\end{frame}
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
        self.gender = choice(["boy", "girl"])
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

    probOf :: (a -> Bool) -> Dist a -> Rational
    probOf p = expect (\x -> if p x then 1 else 0)
  \end{code} 
\end{frame}
\begin{frame}
  \begin{code}
    probOf (all ((==)  Girl  .  gender))  mrJones  ==  frac 1 2
    probOf (all ((==)  Boy   .  gender))  mrSmith  ==  frac 1 3
  \end{code} 
\end{frame}
\subsection{Other Interpreters}
\begin{frame}[allowframebreaks]
  %{
  %format choice_1
  %format choice_2
  \frametitle{Alternative  Interpreters}
  Once the semantics are described, different interpreters are easy to swap in.
  Take Monty Hall, for example:
  \begin{code}
    data Decision = Decision  {  stick   ::  Bool
                              ,  switch  ::  Bool }
    montyHall :: Dist Decision
    montyHall = do
        car           <- uniform [1..3]
        choice_1      <- uniform [1..3]
        let left      = [ door | door <- [1..3], door /= choice_1 ]
        let open      = head [ door | door <- left, door /= car ]
        let choice_2  = head [ door | door <- left, door /= open ]
        return (Decision  {  stick   =  car   ==  choice_1
                          ,  switch  =  car   ==  choice_2 })
  \end{code}
  %}

  While we can interpret it in the normal way to solve the problem:
  \begin{code}
    probOf  stick   montyHall  ==  frac 1 3
    probOf  switch  montyHall  ==  frac 2 3
  \end{code}
  We could alternatively draw a diagram of the process:
  \centering
  \begin{forest}
[$1$
   [$\frac{1}{3}$
      [$\frac{1}{3}$ [{10}]]
      [$\frac{1}{3}$ [{01}]]
      [$\frac{1}{3}$ [{01}]]]
   [$\frac{1}{3}$
      [$\frac{1}{3}$ [{01}]]
      [$\frac{1}{3}$ [{10}]]
      [$\frac{1}{3}$ [{01}]]]
   [$\frac{1}{3}$
      [$\frac{1}{3}$ [{01}]]
      [$\frac{1}{3}$ [{01}]]
      [$\frac{1}{3}$ [{10}]]]]
  \end{forest}
\end{frame}
\section{Theoretical Foundations}
\subsection{Stochastic Lambda Calculus}
\begin{frame}
  \frametitle{Stochastic Lambda Calculus}
  It is possible\footfullcite{ramsey_stochastic_2002} to give measure-theoretic
  meanings to the operations described above.
  \begin{equation}
    \mathcal{M} \left\llbracket \textcolor{Sepia}{\mathit{return}}\: x \right\rrbracket(A) =
      \begin{cases*}
        1, & if $x \in A$ \\
        0, & otherwise
      \end{cases*}
  \end{equation}
    
  \begin{equation}
    \mathcal{M} \left\llbracket d \bind k \right\rrbracket (A) =
    \int_X \mathcal{M} \left\llbracket k(x) \right\rrbracket (A) d \mathcal{M} \left\llbracket d \right\rrbracket (x)
  \end{equation}
  \note{return is the Dirac measure}
\end{frame}
\subsection{Giry Monad}
\begin{frame}
  \frametitle{The Giry Monad}
  $\mathbf{Meas}$ is the category of measurable spaces, where the morphisms are
  measurable maps. There is a functor $\mathbf{P}$ on $\mathbf{Meas}$, where for
  some measurable space $x$, $\mathbf{P}(x)$ is the set of probability measures
  on $x$\footfullcite{dold_categorical_1982}. The monad for $\mathbf{P}$ can be
  defined with two natural transformations
  \begin{gather}
    \eta : A \rightarrow \mathbf{P}(A) \\
    \mu : \mathbf{P}^2(A) \rightarrow \mathbf{P}(A)
  \end{gather}
  Their definitions are from above:
  \begin{gather}
    \eta = \textcolor{Sepia}{\mathit{return}} \\
    \mu(\mathit{P}) = \mathit{P} \bind \mathit{id}
  \end{gather}
\end{frame}
\begin{frame}
  \frametitle{Implementation}
  The implementation of the Giry monad is quite direct:
  \begin{code}
    newtype Measure a = Measure ((a -> Double) -> Double)
  \end{code}
\end{frame}
\section{Other Applications}
\subsection{Differential Privacy}
\begin{frame}
  \frametitle{Differential Privacy}
  It has been shown\footfullcite{reed_distance_2010} that the semantics of the
  probability monad suitable encapsulate \emph{differential privacy}.
\end{frame}
\begin{frame}
  \frametitle{PINQ}
  LINQ\footfullcite{box_linq_2007} is an API which provides a monadic syntax for
  performing queries (sql, etc.)

  PINQ\footfullcite{mcsherry_privacy_2010} extends this to provide
  \emph{differentially private} queries.
\end{frame}
\section{Conclusion}
\end{document}

