\documentclass{report}

\usepackage{ar}
\usepackage[bw]{agda}
\usepackage{ifsym}
\usepackage{amsmath}
\usepackage{amssymb}
\usepackage{parskip}
\usepackage{mathabx}
\usepackage{unicode-math}
\usepackage{newunicodechar}

\newunicodechar{λ}{\ensuremath{\mathnormal\lambda}}
\newunicodechar{∷}{\ensuremath{\mathnormal\Colon}}
\newunicodechar{∨}{\ensuremath{\mathnormal\vee}}
\newunicodechar{ℕ}{\ensuremath{\mathbb{N}}}
\newunicodechar{ℚ}{\ensuremath{\mathbb{Q}}}
\newunicodechar{∈}{\ensuremath{\mathnormal\in}}
\newunicodechar{≡}{\ensuremath{\mathnormal\equiv}}
\newunicodechar{∶}{\ensuremath{\mathnormal\colon\!\!}}
\newunicodechar{ℙ}{\ensuremath{\mathbb{P}}}
\newunicodechar{𝔽}{\ensuremath{\mathbb{F}}}
\newunicodechar{𝕄}{\ensuremath{\mathbb{M}}}
\newunicodechar{𝔹}{\ensuremath{\mathbb{B}}}
\newunicodechar{ν}{\ensuremath{\nu}}
\newunicodechar{μ}{\ensuremath{\mu}}
\newunicodechar{∸}{\ensuremath{\mathnormal\dotdiv}}
\newunicodechar{ᵇ}{\ensuremath{^\mathrm{b}}}
\newunicodechar{≥}{\ensuremath{\mathnormal{\geq}}}
\newunicodechar{ϕ}{\ensuremath{\mathnormal{\phi}}}
\newunicodechar{∧}{\ensuremath{\mathnormal{\wedge}}}
\newunicodechar{∣}{\ensuremath{\mathnormal{|}}}
\newunicodechar{∘}{\ensuremath{\mathnormal{\circ}}}
\newunicodechar{∀}{\ensuremath{\forall}}
\newunicodechar{ℓ}{\ensuremath{\ell}}
\newunicodechar{σ}{\ensuremath{\sigma}}
\newunicodechar{α}{\ensuremath{\alpha}}
\newunicodechar{₁}{\ensuremath{_1}}
\newunicodechar{₂}{\ensuremath{_2}}
\newunicodechar{ₘ}{\ensuremath{_\mathsf{m}}}

\newcommand\Sym\AgdaSymbol
\newcommand\D\AgdaDatatype
\newcommand\F\AgdaFunction
\newcommand\B\AgdaBound

\title{le cmaci jdaske}
\author{la .varik.\ .VALefor.}

\begin{document}

\maketitle

\tableofcontents

\chapter{le me'oi .disclaimer.}
ni'o na mulno

\begin{code}
open import Data.Fin
  using (
    Fin
  )
open import Data.Nat
  using (
    ℕ
  )
open import Function
open import Data.List
  using (
    map;
    List
  )
open import Data.Maybe
  renaming (
    map to mapₘ
  )
open import Data.String
  using (
    String
  )
open import Data.Product
  using (
    Σ;
    _×_;
    _,_;
    proj₁;
    proj₂
  )
open import Data.Rational
  using (
    ℚ
  )
open import Truthbrary.Record.Eq
open import Truthbrary.Record.LLC
  using (
    nu,iork
  )
\end{code}

\chapter{le jicmu}

\section{la'oi .\F{Selcmima}.}
ni'o lo ctaipe be la'oi .\F{Selcmima}.\ cu liste  .i ku'i lo nuncnici cu na vajni fi lo nu facki lo jei dunli

\begin{code}
record Selcmima {a} (A : Set a) : Set a
  where
  field
    liste : List A
\end{code}

\section{la'oi .\F{Bridi}.}
ni'o lo'i ro ctaipe be la'oi .\F{Bridi}.\ cu me'oi .isomorphic.\ lo'i ro bridi

\begin{code}
postulate Bridi : Set
\end{code}

\subsection{le me'oi .\AgdaKeyword{instance}.}

\begin{code}
postulate instance eqBridi : Eq Bridi
\end{code}

\section{la'oi .\F{Selpre}.}
ni'o lo'i ro ctaipe be la'oi .\F{Selpre}.\ cu me'oi .isomorphic.\ lo'i ro selpre

\begin{code}
postulate Selpre : Set
\end{code}

\subsection{le me'oi .\AgdaKeyword{instance}.}

\begin{code}
postulate instance eqSelpre : Eq Selpre
\end{code}

\section{la'oi .\F{Mrena'u}.}
ni'o lo'i ro ctaipe be la'oi .\F{Mrena'u}.\ cu me'oi .isomorphic.\ lo'i ro mrena'u

\begin{code}
postulate Mrena'u : Set
\end{code}

\subsection{le me'oi .\AgdaKeyword{instance}.}

\begin{code}
postulate instance eqMrena'u : Eq Mrena'u
\end{code}

\chapter{le vrici je fancu}

\section{la'oi .\F{grfx}.}
ni'o tu'a la'oi .\F{grfx}.\ filri'a tu'a lo grafu

\begin{code}
grfx : ∀ {a b} → {A : Set a} → (B : Set b) → Selcmima A → Set b
grfx S L = Σ grf $ nu,iork ∘ edgeLoc ∘ Selcmima.liste
  where
  grf = Selcmima $ 𝔽L × 𝔽L × S
    where
    𝔽L = Fin $ Data.List.length $ Selcmima.liste L
  edgeLoc = Data.List.map $ λ q → proj₁ q , proj₁ (proj₂ q)
\end{code}

\chapter{le srana be lo lijda ja zo'e}

\section{la'oi .\F{Jdanunza'omro}.}
ni'o ro da poi ke'a jdanunza'omro zo'u ga jo la'o zoi.\ \B a .zoi.\ ctaipe la'o zoi.\ \F{Jdanunza'omro} .zoi.\ je cu sinxa da gi\ldots
\begin{itemize}
	\item ga je la'o zoi.\ \F{Jdanunza'omro.cmene} \B a .zoi.\ cmene da gi
	\item krici\ldots
	\begin{itemize}
		\item ga je ga jo la'o zoi.\ \B s .zoi.\ selvau la'o zoi.\ \F{Selcmima.liste} \Sym \$ \F{Jdanunza'omro.velski} \B a .zoi.\ gi la'o zoi.\ \B b .zoi.\ jetnu je cu velski da gi
		\item ro de poi ke'a prenu zo'u ga naja de zukte lo nu jetnu fa lo selvau be la'o zoi.\ \F{Selcmima.liste} \Sym \$ \F{Jdanunza'omro.krinu} \B a .zoi.\ gi da jdanunza'omro de
	\end{itemize}
\end{itemize}

\begin{code}
record Jdanunza'omro : Set
  where
  field
    cmene : Selcmima String
    velski : Selcmima Bridi
    krinu : Selcmima Bridi
\end{code}

\subsection{le me'oi .\AgdaKeyword{instance}.}

\begin{code}
postulate instance eqJdanunza'omro : Eq Jdanunza'omro
\end{code}

\section{la'oi .\F{Marde}.}
ni'o lo ro ctaipe be la'oi .\F{Marde}.\ cu marde

.i ga naja la'o zoi.\ \B x .zoi.\ ctaipe la'oi .\F{Marde}.\ gi\ldots
\begin{itemize}
	\item la'o zoi.\ \F{Marde.lenixamgu} \B x .zoi.\ ni la'o zoi.\ \F{Marde.fasnuJaco'e} \B x .zoi.\ vrude lo se marde be la'o zoi.\ \B x .zoi.
\end{itemize}

\begin{code}
record Marde : Set
  where
  field
    fasnuJaco'e : Bridi
    lenixamgu : ℚ
\end{code}

\section{la'oi .\F{Prenu}.}
ni'o lo ro ctaipe be la'oi .\F{Prenu}.\ cu prenu

ni'o ga jo ko'a goi la'o zoi.\ \B a .zoi.\ ctaipe la'oi .\F{Prenu}.\ gi\ldots
\begin{itemize}
	\item ga je lo ro selvau be la'o zoi.\ \F{Sectaipe.liste} \Sym \$ \F{Prenu.cmene} \B a .zoi.\ cu cmene ko'a gi
	\item ga je la'o zoi.\ \F{Prenu.marde} \B a .zoi.\ marde ko'a gi
	\item la'o zoi.\ \F{Prenu.selpre} \B a .zoi.\ selpre ko'a
\end{itemize}

.i la .varik.\ cu sorpa'a lo nu na sarcu fa lo nu ciksi la'o zoi.\ \F{Prenu.,nimarde} .zoi.

\begin{code}
record Prenu : Set
  where
  field
    cmene : Selcmima String
    marde : Selcmima Marde
    selpre : Selpre
  mardyfasnu : List Bridi
  mardyfasnu = Data.List.map Marde.fasnuJaco'e $ Selcmima.liste marde
  field
    ,nimarde : nu,iork mardyfasnu
\end{code}

\subsection{le me'oi .\AgdaKeyword{instance}.}

\begin{code}
postulate instance eqPrenu : Eq Prenu
\end{code}

\section{la'oi .\F{Lijda}.}
ni'o ga jo ko'a goi la'o zoi.\ \B a .zoi.\ ctaipe la'oi .\F{Lijda}.\ gi\ldots
\begin{itemize}
	\item ga je ga jonai ga je\ldots
	\begin{itemize}
		\item ga je lo ro seljda be ko'a cu selcei gi\ldots
		\begin{itemize}
			\item ko'e goi la'o zoi.\ \F{mapₘ} (\F{Selcmima.liste} \Sym ∘ \F{proj₁}) \Sym \$ \F{Lijda.cevni} \B a .zoi.\ cu me'oi .\F{just}.\ la'o zoi.\ \B C .zoi.\ goi lo liste be lo cevni ja co'e be ko'a gi
			\item ga jo la'o zoi.\ \F{mapₘ} (\F{Selcmima.liste} ∘ \F{proj₂}) \Sym \$ \F{Lijda.cevni}) \B a .zoi.\ me'oi .\F{just}.\ lo vasru be la'o zoi.\ \B J .zoi.\ gi la'o zoi.\ \F{Data.List.lookup} \B C \Sym \$ \F{proj₂} \Sym \$ \F{proj₂} \Sym \$ \F{proj₂} \B J .zoi.\ ni la'o zoi.\ \F{proj₁} \B J .zoi.\ nelci la'o zoi.\ \F{Data.List.lookup} \B C \Sym \$ \F{proj₁} \Sym \$ \F{proj₂} \Sym \$ \F{proj₂} \B J .zoi.\ gi
		\end{itemize}
		\item gi ko'e du la'oi .\F{nothing}.\ gi
        \end{itemize}
	\item ga je la'o zoi.\ \F{Lijda.marde} .zoi.\ marde lo seljda be ko'a gi
	\item ga jonai ga je lo su'o co'e cu jdanunza'omro fi ko'a gi ko'e goi la'o zoi.\ \F{mapₘ} \F{Selcmima.liste} \Sym \$ Lijda.jdanunza'omro \B a .zoi.\ me'oi .\F{just}.\ lo vasru be lo jdanunza'omro be fi ko'a gi ko'e du la'oi .\F{nothing}.
\end{itemize}

\begin{code}
record Lijda : Set
  where
  field
    cevni : Maybe $ Σ (Selcmima Prenu) $ grfx ℚ
    marde : Selcmima Marde
    jdanunza'omro : Maybe $ Selcmima Jdanunza'omro
\end{code}
\end{document}