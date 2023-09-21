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
\newunicodechar{⦃}{\ensuremath{\mathnormal{\lbrace\!\lbrace}}}
\newunicodechar{⦄}{\ensuremath{\mathnormal{\rbrace\!\rbrace}}}

\newcommand\Sym\AgdaSymbol
\newcommand\D\AgdaDatatype
\newcommand\F\AgdaFunction
\newcommand\B\AgdaBound
% | ni'o cadga fa lo nu la'oi .BlS. mo  .i selneimau fi la .varik.
\newcommand\OpF[1]{\AgdaOperator{\AgdaFunction{#1}}}

\title{le cmaci jdaske}
\author{la .varik.\ .VALefor.}

\begin{document}

\maketitle

\tableofcontents

\chapter{le me'oi .disclaimer.}
ni'o na mulno

\chapter{le vrici}

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
  using (
    Eq
  )
open import Truthbrary.Record.LLC
  using (
    nu,iork;
    length
  )
\end{code}

\chapter{le jicmu}

\section{la'oi .\AgdaRecord{Multiset}.}
ni'o lo ro ctaipe be la'oi .\AgdaRecord{Multiset}.\ cu me'oi .multiset.\  .i lo me'oi .multiset.\ cu smimlu lo liste  .i ku'i lo nuncnici be lo me'oi .multiset.\ cu na vajni fi lo nu facki lo jei dunli

\begin{code}
record Multiset {a} (A : Set a) : Set a
  where
  field
    liste : List A
\end{code}

\section{la'oi .\AgdaRecord{Selcmima}.}
ni'o la'oi .\AgdaRecord{Selcmima}.\ smimlu la'oi .\AgdaRecord{Multiset}.  .i ku'i ga jo la'o zoi.\ \B a .zoi.\ ctaipe la'o zoi.\ \AgdaKeyword{Selcmima} \B A .zoi.\ gi la'o zoi.\ \F{Selcmima.narpanra} \B a .zoi.\ ctaipe lo du'u ro da poi ke'a cmima ja co'e la'o zoi.\ \F{Selcmima.liste} \B a .zoi.\ zo'u li pa nilzilcmi lo'i ro selvau be la'o zoi.\ \F{Selcmima.liste} \B a .zoi.\ poi ke'a du da

\begin{code}
record Selcmima {a} (A : Set a) ⦃ _ : Eq A ⦄ : Set a
  where
  field
    liste : List A
    narpanra : nu,iork liste
\end{code}

\section{la'oi .\F{Fasnu}.}
ni'o ro da zo'u da ctaipe la'oi .\F{Fasnu}.\ jo cu fasnu

\begin{code}
postulate Fasnu : Set
\end{code}

\subsection{le me'oi .\AgdaKeyword{instance}.}

\begin{code}
postulate instance eqFasnu : Eq Fasnu
\end{code}

\section{la'oi .\F{Selpre}.}
ni'o ro da zo'u da ctaipe la'oi .\F{Selpre}.\ jo cu selpre

\begin{code}
postulate Selpre : Set
\end{code}

\subsection{le me'oi .\AgdaKeyword{instance}.}

\begin{code}
postulate instance eqSelpre : Eq Selpre
\end{code}

\chapter{le srana be lo lijda ja zo'e}

\section{la'oi .\AgdaRecord{Jdanunza'omro}.}
ni'o ga jo ko'a goi la'o zoi.\ \B a .zoi.\ ctaipe la'o zoi.\ \AgdaRecord{Jdanunza'omro} .zoi.\ gi ga je ko'a jdanuza'omro gi\ldots
\begin{itemize}
	\item ga je la'o zoi.\ \F{Jdanunza'omro.cmene} \B a .zoi.\ cmene ko'a gi
	\item krici le du'u\ldots
	\begin{itemize}
		\item ga je ga jo la'o zoi.\ \B s .zoi.\ selvau la'o zoi.\ \F{Selcmima.liste} \OpF \$ \F{Jdanunza'omro.velski} \B a .zoi.\ gi la'o zoi.\ \B s .zoi.\ jetnu je cu velski ko'a gi
		\item ro da poi ke'a prenu zo'u ga naja da zukte lo cmima be la'o zoi.\ \F{Selcmima.liste} \OpF \$ \F{Jdanunza'omro.krinu} \B a .zoi.\ gi ko'a jdanunza'omro da
	\end{itemize}
\end{itemize}

\begin{code}
record Jdanunza'omro : Set
  where
  field
    cmene : Selcmima String
    velski : Selcmima Fasnu
    krinu : Selcmima Fasnu
\end{code}

\subsection{le me'oi .\AgdaKeyword{instance}.}

\begin{code}
postulate instance eqJdanunza'omro : Eq Jdanunza'omro
\end{code}

\section{la'oi .\F{Marde}.}
ni'o ga jo la'oi .\OpF{f}.\ ctaipe la'oi .\F{Marde}.\ gi la'o zoi.\ \OpF f \B x\ .zoi.\ ni la'oi .\B{x}.\ vrude la'oi .\F{f}.

\begin{code}
Marde : Set
Marde = Fasnu → ℚ
\end{code}

\subsection{le me'oi .\AgdaKeyword{instance}.}

\begin{code}
postulate instance eqMarde : Eq Marde
\end{code}

\section{la'oi .\F{Prenu}.}
ni'o ga jo ko'a goi la'o zoi.\ \B a .zoi.\ ctaipe la'oi .\AgdaRecord{Prenu}.\ gi\ldots
\begin{itemize}
	\item ga je ko'a se cmene lo ro cmima be la'o zoi.\ \F{Selcmima.liste} \OpF \$ \F{Prenu.cmene} \B a .zoi.\ gi
	\item ga je la'o zoi.\ \F{Prenu.marde} \B a .zoi.\ marde ko'a gi
	\item la'o zoi.\ \F{Prenu.selpre} \B a .zoi.\ selpre ko'a
\end{itemize}

\begin{code}
record Prenu : Set
  where
  field
    cmene : Selcmima String
    marde : Marde
    selpre : Selpre
\end{code}

\subsection{le me'oi .\AgdaKeyword{instance}.}

\begin{code}
postulate instance eqPrenu : Eq Prenu
\end{code}

\section{la'oi .\F{Lijda}.}
ni'o ga jo ko'a goi la'o zoi.\ \B a .zoi.\ ctaipe la'oi .\AgdaRecord{Lijda}.\ gi\ldots
\begin{itemize}
	\item ga je ga jonai ga je\ldots
	\begin{itemize}
		\item ga je lo ro seljda be ko'a cu selcei gi\ldots
		\begin{itemize}
			\item ko'e goi la'o zoi.\ \F{mapₘ} \Sym(\F{Selcmima.liste} \OpF ∘ \F{proj₁}\Sym) \OpF \$ \F{Lijda.cevni} \B a .zoi.\ cu me'oi .\F{just}.\ lo liste be lo cevni ja co'e be ko'a gi
			\item ga jo la'o zoi.\ \B t\ .zoi.\ ctaipe la'o zoi.\ \F{Is-just} \OpF \$ \F{Lijda.cevni} \B a\ .zoi.\ gi ga jo la'o zoi.\ \B Z\ .zoi.\ du la'o zoi.\ \F{Data.Maybe.to-witness} \B t\ .zoi.\ gi la'o zoi.\ \Sym(\F{proj₂} \B Z\Sym) \B x \B y\ .zoi.\ ni la'o zoi.\ \F{proj₁} \B Z \OpF !\ \B x\ .zoi.\ nelci la'o zoi.\ \F{proj₁} \B Z \OpF !\ \B y\ .zoi.\ gi
		\end{itemize}
		\item ko'e du la'oi .\F{nothing}.\ gi
	\end{itemize}
	\item ga je la'o zoi.\ \F{Lijda.marde} .zoi.\ marde lo seljda be ko'a gi
	\item ga jonai ga je su'o da zo'u da jdanunza'omro fi ko'a gi ko'e goi la'o zoi.\ \F{mapₘ} \F{Selcmima.liste} \OpF \$ Lijda.jdanunza'omro \B a .zoi.\ me'oi .\F{just}.\ lo'i jdanunza'omro be fi ko'a gi ko'e du la'oi .\F{nothing}.
\end{itemize}

\begin{code}
record Lijda : Set
  where
  private
    𝔽L : ∀ {a} → {A : Set a} → ⦃ _ : Eq A ⦄ → Selcmima A → Set
    𝔽L = Fin ∘ length ∘ Selcmima.liste
  field
    cevni : Maybe $ Σ (Selcmima Prenu) $ (λ X → X → X → ℚ) ∘ 𝔽L
    marde : Marde
    jdanunza'omro : Maybe $ Selcmima Jdanunza'omro
\end{code}
\end{document}
