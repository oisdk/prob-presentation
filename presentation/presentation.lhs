\documentclass[usenames,dvipsnames]{beamer}
\usepackage{xcolor}
\usepackage{amsmath}
\usepackage{forest}
\usepackage{mathtools}
\usepackage{minted}
\usepackage{tikz}
\usepackage{tikz-cd}
\setminted{autogobble}
% \setbeameroption{show notes}
\usetheme{metropolis}

%include polycode.fmt

%subst keyword a = "\textcolor{BlueViolet}{\textbf{" a "}}"
%format frac (a) (b) = "\frac{" a "}{" b "}"
%format * = "\times"
%format Double = "\mathbb{R}"
%format Rational = "\mathbb{R}"

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
  \begin{minted}{python}
    from random import randrange, choice

    class Child:
        def __init__(self):
            self.gender = choice(['boy', 'girl'])
            self.age = randrange(18)
  \end{minted}
  \begin{minted}{python}
    from operator import attrgetter

    def mr_jones():
        child_1 = Child()
        child_2 = Child()
        eldest = max(child_1, child_2,
                    key=attrgetter('age'))
        assert eldest.gender == 'girl'
        return [child_1, child_2]
  \end{minted}
  \begin{minted}{python}
    def mr_smith():
        child_1 = Child()
        child_2 = Child()
        assert child_1.gender == 'boy' or \
               child_2.gender == 'boy'
        return [child_1, child_2]
  \end{minted}
\end{frame}
\subsection{Unclear Semantics}
\begin{frame}[fragile]
  \frametitle{Unclear semantics}
  What contracts are guaranteed by probabilistic functions? What does it mean
  \emph{exactly} for a function to be probabilistic? Why isn't the
  following\footfullcite{munroe_xkcd_2007} ``random''?
  \begin{minted}{c}
    int getRandomNumber()
    {
      return 4; // chosen by fair dice roll.
                // guaranteed to be random.
    }
  \end{minted} 
\end{frame}
\begin{frame}[fragile]
  What about this?
  \begin{minted}{python}
    children_1 = [Child(), Child()]
    children_2 = [Child()] * 2
  \end{minted}
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
  \begin{minted}{python}
    def expect(predicate, process, iterations=100):
        success, tot = 0, 0
        for _ in range(iterations):
            try:
                success += predicate(process())
                tot += 1
            except AssertionError:
                pass
        return success / tot
  \end{minted}
  \note{This solution is both inefficient and inexact. Also, we may want to
    express other attributes of probability distributions: independence, for
    example.}
\end{frame}
\begin{frame}[fragile]
  \frametitle{The Ad-Hoc Solution}
  \begin{minted}{python}
    p_1 = expect(
        lambda children: all(child.gender == 'girl'
                            for child in children),
        mr_jones)
    p_2 = expect(
        lambda children: all(child.gender == 'boy'
                            for child in children),
        mr_smith)
  \end{minted}
  \begin{gather*}
    \mintinline{python}{p_1} \approxeq \frac{1}{2} \\
    \mintinline{python}{p_2} \approxeq \frac{1}{3}
  \end{gather*}
\end{frame}
\section{Monadic Modeling}
\begin{frame}
  \frametitle{A DSL}
  What we're approaching is a DSL, albeit an unspecified one.

  \pause
  Three questions for this DSL:
  \pause
  \begin{itemize}
    \item Why should we implement it? What is it useful for?
    \pause
    \item How should we implement it? How can it be made efficient? 
    \pause
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
  \note{This representation only works for discrete distributions}
\end{frame}
\begin{frame}
  We could (for example) encode a die as:
  \begin{code}
    die :: Dist Integer
    die = Dist [(1,frac 1 6), (2,frac 1 6), (3,frac 1 6), (4,frac 1 6), (5,frac 1 6), (6,frac 1 6)]
  \end{code}
\end{frame}
\begin{frame}
  This lets us encode (in the types) the difference between:
\begin{code}
  children_1 :: [Dist Child]
  children_2 :: Dist [Child]
\end{code}
\end{frame}
\begin{frame}[fragile]
  As we will use this as a DSL, we need to define the language features we used
  above:
  \begin{onlyenv}<1>
    \begin{minted}{python}
      def mr_smith():
          child_1 = Child()
          child_2 = Child()
          assert child_1.gender == 'boy' or \
                 child_2.gender == 'boy'
          return [child_1, child_2]
    \end{minted}
  \end{onlyenv}
  \begin{onlyenv}<2>
    \begin{minted}[highlightlines={2,3}, highlightcolor=Goldenrod]{python}
      def mr_smith():
          child_1 = Child()
          child_2 = Child()
          assert child_1.gender == 'boy' or \
                 child_2.gender == 'boy'
          return [child_1, child_2]
    \end{minted}
  \end{onlyenv}
  \begin{onlyenv}<3>
    \begin{minted}[highlightlines={4,5}, highlightcolor=Goldenrod]{python}
      def mr_smith():
          child_1 = Child()
          child_2 = Child()
          assert child_1.gender == 'boy' or \
                 child_2.gender == 'boy'
          return [child_1, child_2]
    \end{minted}
  \end{onlyenv}
  \begin{onlyenv}<4>
    \begin{minted}[highlightlines={6}, highlightcolor=Goldenrod]{python}
      def mr_smith():
          child_1 = Child()
          child_2 = Child()
          assert child_1.gender == 'boy' or \
                 child_2.gender == 'boy'
          return [child_1, child_2]
    \end{minted}
  \end{onlyenv}
  \begin{enumerate}
    \item<2-> \verb+=+ (assignment)
    \item<3-> \verb+assert+
    \item<4-> \verb+return+
  \end{enumerate}
\end{frame}
\begin{frame}[allowframebreaks]
  \frametitle{Assignment}
  Assignment expressions can be translated into lambda expressions:
  %format e_1
  %format e_2
  %format --> = "."
  \begin{code}
      let x = e_1 in e_2
    ==
      (\x--> e_2) e_1
  \end{code}
  In the context of a probabilistic language, $\textcolor{Sepia}{\mathit{e}}_1$
  and $\textcolor{Sepia}{\mathit{e}}_1$ are distributions. So what we need to
  define is application: this is encapsulated by the ``monadic bind'':
  \begin{code}
    (>>=) :: Dist a -> (a -> Dist b) -> Dist b
  \end{code}
  For a distribution, what's happening inside the $\lambda$ is
  $\textcolor{Sepia}{\mathit{e}}_1$ given $\textcolor{Sepia}{\mathit{x}}$.
  Therefore, the resulting probability is the product of the outer  and inner
  probabilities.
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
\begin{frame}
  \frametitle{Alternative  Interpreters}
  Once the semantics are described, different interpreters are easy to swap in.
\end{frame}
\begin{frame}[allowframebreaks]
  \frametitle{Monty Hall}
  %{
  %format choice_1
  %format choice_2
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

  \framebreak
  While we can interpret it in the normal way to solve the problem:
  \begin{code}
    probOf  stick   montyHall  ==  frac 1 3
    probOf  switch  montyHall  ==  frac 2 3
  \end{code}

  \framebreak
  We could alternatively draw a diagram of the process.
  \begin{figure}
    \centering
    \begin{forest}
      [$1$
        [$\frac{1}{3}$
            [$\frac{1}{3}$ [{\verb|10|}]]
            [$\frac{1}{3}$ [{\verb|01|}]]
            [$\frac{1}{3}$ [{\verb|01|}]]]
        [$\frac{1}{3}$
            [$\frac{1}{3}$ [{\verb|01|}]]
            [$\frac{1}{3}$ [{\verb|10|}]]
            [$\frac{1}{3}$ [{\verb|01|}]]]
        [$\frac{1}{3}$
            [$\frac{1}{3}$ [{\verb|01|}]]
            [$\frac{1}{3}$ [{\verb|01|}]]
            [$\frac{1}{3}$ [{\verb|10|}]]]]
    \end{forest}
    \caption{
      AST from Monty Hall problem. \verb|1| is a win, \verb|0| is a loss. The
      first column is what happens on a stick, the second is what happens on a
      loss.
    }
  \end{figure}
\end{frame}
\section{Theoretical Foundations}
\subsection{Stochastic Lambda Calculus}
\begin{frame}
  \frametitle{Stochastic Lambda Calculus}
  It is possible\footfullcite{ramsey_stochastic_2002} to give measure-theoretic
  meanings to the operations described above.
  \begin{gather}
    \mathcal{M} \left\llbracket \textcolor{Sepia}{\mathit{return}}\: x \right\rrbracket(A) =
      \begin{cases*}
        1, & if $x \in A$ \\
        0, & otherwise
      \end{cases*} \\
    \mathcal{M} \left\llbracket d \bind k \right\rrbracket (A) =
    \int_X \mathcal{M} \left\llbracket k(x) \right\rrbracket (A) d \mathcal{M} \left\llbracket d \right\rrbracket (x)
  \end{gather}
  \note{return is the Dirac measure}
\end{frame}
\subsection{Giry Monad}
\begin{frame}
  \frametitle{The Giry Monad}
  Giry\footfullcite{dold_categorical_1982} gave a categorical interpretation of
  probability theory.
\end{frame}
\begin{frame}[fragile]
  \frametitle{Categories, Quickly}
  \pause
  \begin{columns}
    \column{0.3\textwidth}
    \begin{equation*}
      \begin{tikzcd}
        X \arrow[r, "f"] \arrow[rd, "g \circ f"'] & Y \arrow[d, "g"] \\
                                                  & Z
      \end{tikzcd}
    \end{equation*}
    \column{0.7\textwidth}
    \begin{description}
      \pause
      \item[Objects] $\mathbf{Ob}(\mathbf{C}) = \{X, Y, Z\}$
      \pause
      \item[Arrows] $\mathbf{hom}_{\mathbf{C}}(X, Y) = X \rightarrow Y$
      \pause
      \item[Composition] $\circ$
    \end{description}
  \end{columns}
  \pause
  \begin{block}{Arrows form a monoid under composition}
    \begin{columns}
      \column{0.5\textwidth}
      \begin{equation*}
        \begin{tikzcd}
          W \ar[r, "f"] \ar[rd, "g \circ f"'] & X \ar[d, "g"]  \ar[rd, "h \circ g"] & \\
                                              & Y \ar[r, "h"] & Z
        \end{tikzcd}
      \end{equation*}
      \column{0.5\textwidth}
        \begin{equation}
          (h \circ g) \circ f = h \circ (g \circ f)
        \end{equation}
    \end{columns}
    \begin{columns}
      \column{0.5\textwidth}
      \begin{equation*}
        \begin{tikzcd}
          A \arrow[loop right, "id_A"]
        \end{tikzcd}
      \end{equation*}
      \column{0.5\textwidth}
      \begin{equation}
        \forall A. A \in \mathbf{Ob}(\mathbf{C}) \: \exists \; \mathit{id}_A : \mathbf{hom}_{\mathbf{C}}(A, A)
      \end{equation}
    \end{columns}
  \end{block}
  \pause
  \begin{block}{Example}
    $\mathbf{Set}$ is the category of sets, where objects are sets, and arrows
    are functions.
  \end{block}
\end{frame}
\begin{frame}[fragile]
  \frametitle{Functors}
  The category of (small) categories, $\mathbf{Cat}$, has morphisms called
  Functors.
  \pause

  These can be thought of as ways to ``embed'' one category into another.
  \pause

  \begin{equation*}
    \begin{tikzcd}
      \mathbf{F}X \ar[r, "\mathbf{F}f"] & \mathbf{F}Y \\
      X \ar[r, "f"] \ar[u]              & Y \ar[u]
    \end{tikzcd}
  \end{equation*}
  
  Functors which embed categories into themselves are called Endofunctors.
\end{frame}
\begin{frame}
  \frametitle{Monads}
  In the category of Endofunctors, $\mathbf{Endo}$, a Monad is a triple of:
  \begin{enumerate}
    \item An Endofunctor $\mathit{m}$,
    \item A natural transformation:
      \begin{equation}
        \eta : A \rightarrow \mathit{m}(A)
      \end{equation}
      This is an operation which embeds an object.
    \item Another natural transformation:
      \begin{equation}
        \mu : \mathit{m}^2(A) \rightarrow \mathit{m}(A)
      \end{equation}
      This collapses two layers of the functor.
  \end{enumerate}
\end{frame}
\begin{frame}
  \frametitle{The Category of Measurable Spaces}
  $\mathbf{Meas}$ is the category of measurable spaces.

  \pause
  The arrows ($\mathbf{hom}_{\mathbf{Meas}}$) are measurable maps.

  \pause
  The objects are measurable spaces.

  \pause
  We can construct a functor ($\mathcal{P}$), which, for any given measurable
  space $\mathcal{M}$, is the space of all possible measures on it.

  \pause
  $\mathcal{P}(\mathcal{M})$ is itself a measurable space: measuring is
  integrating over some variable $\textcolor{Sepia}{\mathit{a}}$ in
  $\mathcal{M}$.

  \pause
  In code (we restrict to measurable functions):
  \begin{code}
    newtype Measure a = Measure ((a -> Rational) -> Rational)
  \end{code}
\end{frame}
\begin{frame}
  We now get $\eta$ and $\mu$:

  \begin{code}
    integrate :: Measure a -> (a -> Rational) -> Rational
    integrate (Measure m) f = m f

    return :: a -> Measure a
    return x = Measure (\measure -> measure x)

    (>>=) :: Measure a -> (a -> Measure b) -> Measure b
    xs >>= f = Measure  (\measure -> integrate xs
                        (\x -> integrate (f x)
                        (\y -> measure y)))
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

