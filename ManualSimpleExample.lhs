% Copyright 2011, University of Bergen. All rights reserved.

% Redistribution and use in source and binary forms, with or without modification, are
% permitted provided that the following conditions are met:

%    1. Redistributions of source code must retain the above copyright notice, this list of
%       conditions and the following disclaimer.

%    2. Redistributions in binary form must reproduce the above copyright notice, this list
%       of conditions and the following disclaimer in the documentation and/or other materials
%       provided with the distribution.

% THIS SOFTWARE IS PROVIDED BY University of Bergen ``AS IS'' AND ANY EXPRESS OR IMPLIED
% WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND
% FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL University of Bergen OR
% CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR
% CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
% SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON
% ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
% NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF
% ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

% The views and conclusions contained in the software and documentation are those of the
% authors and should not be interpreted as representing official policies, either expressed
% or implied, of University of Bergen.

\documentclass[a4paper,10pt]{article}
\usepackage{url}
\usepackage{hyperref}
\usepackage{verbatim}
\usepackage{ucs}
\usepackage[utf8x]{inputenc}
\usepackage{listings}
\usepackage{latexsym}
\usepackage{amsmath,amsfonts,amssymb}
\usepackage{multirow}
\usepackage{graphics}

\newtheorem{lemma}{Lemma}

\lstloadlanguages{Haskell}
\lstnewenvironment{code}
    {\lstset{}%
      \csname lst@SetFirstLabel\endcsname}
    {\csname lst@SaveFirstLabel\endcsname}
    \lstset{
      basicstyle=\small\ttfamily, %\small\ttfamily,
      flexiblecolumns=false,
      basewidth={0.5em,0.45em},
      literate={+}{{$+$}}1 {/}{{$/$}}1 {*}{{$*$}}1 {=}{{$=$}}1
               {>}{{$>$}}1 {<}{{$<$}}1 {\\}{{$\lambda$}}1
               {\\\\}{{\char`\\\char`\\}}1
               {->}{{$\rightarrow$}}2 {>=}{{$\geq$}}2 {<-}{{$\leftarrow$}}2
               {<=}{{$\leq$}}2 {=>}{{$\Rightarrow$}}2
               {\ .}{{$\circ$}}2 {\ .\ }{{$\circ$}}2
               {>>}{{>>}}2 {>>=}{{>>=}}2
               {|}{{$\mid$}}1
               {power_0}{{power$_0$}}7
               {power_0'}{{power'$_0$}}7
               {power_1}{{power$_1$}}7
               {power_2}{{power$_2$}}7
               {power_3}{{power$_3$}}7
    }

\PrerenderUnicode{Å}
\PrerenderUnicode{ź}

\newcommand{\cc}[1]{\lstinline!#1!}

\newcommand{\acro}[1]{\textsc{#1}}
\newcommand{\mcname}{\acro{NorMC}}
\newcommand{\dia}[1]{\langle #1\rangle}
\newcommand{\todo}[1]{\textbf{TODO: \emph{#1}}}

\renewcommand{\phi}{\varphi}

\begin{document}
\title{\mcname\ User Guide}
\author{Piotr Kaźmierczak, Truls Pedersen and Thomas Ågortnes}
\date{}
\maketitle

This file is a Literate Haskell program.

\section{Installation and Usage}

NorMC is written in Haskell, and it needs a Glasgow Haskell Compiler interpreter to run. You can download GHC from its homepage at \url{http://www.haskell.org/ghc/}, but a simpler and better way is to download the whole Haskell Platform: \url{http://hackage.haskell.org/platform/}. Both Haskell and GHC are free to use and available for Windows, Mac, Linux, and other platforms.

In order to run NorMC, you have to load its files into the GHC interpreter:
\begin{small}
\begin{verbatim}
$ ghci NCCTL.hs
\end{verbatim}
\end{small}

You can also load the examples mentioned in the paper, either from the shell (as above) or from within the GHCi command line:

\begin{small}
\begin{verbatim}
Prelude> :l Ex02.hs
\end{verbatim}
\end{small}

Current version of NorMC cannot be compiled as a standalone Haskell program, and it always needs GHC to run. Also, NorMC is not compatible with Hugs, and has not been tested with any other Haskell interpreters.

\section{Simple Example}

In order to demonstrate the use of the model checker, we now present a
simple example that introduces basic concepts and constructs. It is a
toy example that proves a rather well known fact that two people can
pass each other on the sidewalk. We begin with importing the model
checker files along with a standard Haskell library for handling
lists.

\begin{code}

module ManualSimpleExample where

import NCCTL hiding (owner)
import FODBR (FODBR, build, find1, nubisect)
import Data.List (sort, (\\))
\end{code}

The core of the model checker is a function called
\cc{check}.  By importing the \mcname\ code into a Haskell interpreter,
this function can be used as follows:
\begin{small}
\begin{verbatim}
*Example> check myModel myNS myFormula
[s1, s3, s7]
\end{verbatim}
\end{small}
Here, the arguments \cc{myModel}, \cc{myNS} and \cc{myFormula},
represent the model, the normative system, and the formula
respectively, and the function returns the set of (in this case three)
states in which the formula holds in the given model and normative
system.  We now describe the types of these three arguments expected
by \cc{check}.

Kripke models are represented by the \cc{Kripke} data structure.  To
represent sets, such as the set of states in the \cc{Kripke}
structure, sorted lists with no duplicate occurrences are used.  In
\mcname\ \cc{Kripke} is defined as follows:
\begin{small}
\begin{verbatim}
data (Ord s, Eq p) => Kripke p s = Kripke {
  agents :: [Int],       states :: [s],
  tr :: FODBR s s,       owner :: (s, s) -> Int,
  valuation :: p -> [s]  }
\end{verbatim}
\end{small}

Also, we provide an abbreviation for the 'backward' and 'forward' state:

\begin{small}
\begin{verbatim}
forwards,backwards :: (Ord s, Eq p) => Kripke p s -> SBMT s s
forwards = fst . tr
backwards  = snd . tr
\end{verbatim}
\end{small}

As an example, we describe a simple model of a pavement,
divided into 10 \textit{positions}, with two agents on opposite
sides of it. The agents can move (or choose to stand still)
alternatingly. The model, in its initial state, can be visualised as
follows:

\begin{center}
\scalebox{0.32}{\includegraphics{agmod.pdf}}
\end{center}

The model is defined by the following declaration.
\begin{code}
exampleModel :: Kripke Prop State
exampleModel = Kripke [0,1] statespace transition owner val
\end{code}

The \cc{transition} relation over the \cc{statespace} describes the
possible transitions resulting from agents' actions.  In addition to
these components we also need to assign the \cc{owner} of each
transition step.  The proposition symbols and their valuation map
complete the definition of the model.

Regarding the type of the propositions, \cc{Prop}, we would like to talk
about whether a particular agent is found on the east/west edge of the
pavement, or in the north/south ``lane''. The type of the states,
\cc{State}, must be able to code the current agent and the positions
of both the agents. We can represent this by three integers.

\begin{code}
data Property = N | S | E | W | T deriving (Eq, Show)

type Prop  = (Property, Int)
type State = (Int, Int, Int)
\end{code}

A state is thus a tuple consisting of three integers. The
first indicates the position of agent \cc{0}, the second the position of agent 1, and the last indicates which agent's turn it is. The sorted list of possible states of the model can be
described by Haskell's list comprehension syntax succinctly:

\begin{code}
statespace :: [State]
statespace = [ (p0, p1, i) | p0 <- [0..9], p1 <- [0..9], p0 /= p1, i <- [0,1] ]
\end{code}

In the initial state, it is \cc{0}'s turn, agent \cc{0} is in position
0, and agent \cc{1} is in position 9.

\begin{code}
initState :: State
initState = (0, 9, 0)
\end{code}

The valuation function selects the states from \cc{statespace} in which
the indicated agent is in one of the appropriate positions.

\begin{code}
project :: Int -> State -> Int
project 0 (p0, _, _) = p0
project 1 (_, p1, _) = p1

val :: Prop -> [State]
val (N, ag) = filter (even . project ag) statespace
val (S, ag) = filter (odd . project ag) statespace
val (W, ag) = filter ((`elem` [0,1]) . project ag) statespace
val (E, ag) = filter ((`elem` [8,9]) . project ag) statespace
val (T, ag) = filter (\(_,_,i) -> i == ag) statespace
\end{code}

The \cc{transition} relation indicates which transitions are available
to the agents, or simply what 'moves' agents can perform.

\begin{code}
transition = build [((p0,p1,i), (p0',p1',1-i)) |
                    (p0,p1,i) <- statespace,
                    p0'       <- possibleSteps (i == 0) p0,
                    p1'       <- possibleSteps (i == 1) p1,
                    (p0',p1',1-i) `elem` statespace]
\end{code}

\cc{possibleSteps} is a helper function for \cc{transition}, and says
that agents can 'stand', 'move' west, east, and so on. If it's not the
agent's turn (first argument is \cc{False}) the only possible move is
standing.

\begin{code}
possibleSteps :: Bool -> Int -> [Int]
possibleSteps False p = [p]
possibleSteps True p = [p-2, p, p+2]++(if even p then [p+1] else [p-1])
\end{code}

Normative systems are represented in the same way as the transition
relation, through the \cc{FODBR} type.  The following relation
\cc{illegal} specifies a normative system for the example: any agent
must not place himself directly in front of the other agent, and if an
agent is able to move in the general direction required for the
satisfaction of the goal, he must do so.

\begin{code}
illegal :: FODBR State State
illegal = build [ ((p0,p1,i),(p0',p1',1-i)) |
                  (p0,p1,i)   <- statespace,
                  (p0',p1',_) <- find1 (fst transition) (p0,p1,i),
                  p1' == p0' + 2 || if i == 0 then p0' < 8 && p0 >= p0'
                                              else p1' > 1 &&  p1 <= p1']

owner :: (State,State) -> Int
owner ((_,_,i),_) = i
\end{code}

Finally, formulas are represented by the structures \cc{Formula} and
\cc{Coalition}:
\begin{small}
\begin{verbatim}
data (Eq p) => Formula p = Prop p           | Neg  (Formula p)
             | Disj (Formula p) (Formula p) | Conj (Formula p) (Formula p)
             | EX   (Formula p)             | EF   (Formula p)
             | EG   (Formula p)             | EU   (Formula p) (Formula p)
             | CD   Coalition   (Formula p) | CS   Coalition   (Formula p)
               deriving (Show)

data Coalition = Subseteq [Int]             | Supseteq [Int]
               | Eq [Int]                   | GEQ Int
               | CNeg Coalition             | CDisj Coalition Coalition
                 deriving (Show)

ag,af :: (Eq p) => (Formula p) -> (Formula p)
ag f = Neg (EF (Neg f))
af f = Neg (EG (Neg f))
\end{verbatim}
\end{small}
A formula that should be true only in the initial state in the example:
\begin{code}
initF :: Formula Prop
initF = Conj (Conj (Prop (T, 0)) (Conj (Prop (N, 0)) (Prop (W, 0))))
             (Conj (Prop (S, 1)) (Prop (E, 1)))
\end{code}
%
And now an \emph{objective} formula: agent \cc{0} is east, and \cc{1} is west:
\begin{code}
goalF :: Formula Prop
goalF = Conj (Prop (E, 0)) (Prop (W, 1))
\end{code}

We now have all three arguments for the \cc{check} function:
\begin{small}
\begin{verbatim}
*Ex01> check exampleModel illegal (Conj initF (af goalF))
[]
*Ex01> check exampleModel illegal (CD (GEQ 0) (Conj initF (af goalF)))
[(0,9,0)]
\end{verbatim}
\end{small}
%
We can see that there is no state satisfying both \cc{initF} and
\cc{af goalF}, but there exists a coalition which can ensure that we
eventually end up satisfying the goal.

\end{document}
