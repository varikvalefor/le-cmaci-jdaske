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
  using (
    Maybe
  )
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
    length;
    LL;
    UL
  )
\end{code}

\chapter{le jicmu}

\section{la'oi .\AgdaRecord{Multiset}.}
ni'o ga jo ko'a goi la'o zoi.\ \B x\ .zoi.\ ctaipe la'o zoi.\ \AgdaRecord{Multiset} \B X\ .zoi.\ gi ko'a me'oi .multiset.\ je cu se cmima lo ro cmima be la'o zoi.\ \F{Multiset.liste} \B x\ .zoi.\ be'o ku po'o  .i lo me'oi .multiset.\ cu smimlu lo liste  .i ku'i lo co'e ja se porsi be lo me'oi .multiset.\ cu na vajni fi lo nu facki lo jei dunli

\begin{code}
record Multiset {a} (A : Set a) : Set a
  where
  field
    liste : List A
\end{code}

\subsection{le su'u pilno le zo'oi .\AgdaKeyword{record}.\ co'e}
ni'o le su'u la .varik.\ cu me'oi .\AgdaKeyword{record}.\ ciksi la'oi .\AgdaRecord{Multiset}.\ jenai cu gasnu lo nu la'oi .\F{Multiset}.\ du la'oi .\D{List}.\ cu se krinu le su'u la .varik.\ cu toldji lo nu frili fa lo nu vukna ja co'e lo ctaipe be la'o zoi.\ \AgdaRecord{Multiset} \B x\ .zoi.\ lo ctaipe be la'o zoi.\ \D{List} \B x\ .zoi.

\section{la'oi .\AgdaRecord{Selcmima}.}
ni'o la'oi .\AgdaRecord{Selcmima}.\ smimlu la'oi .\AgdaRecord{Multiset}.  .i ku'i ga jo la'o zoi.\ \B a .zoi.\ ctaipe la'o zoi.\ \AgdaRecord{Selcmima} \B A .zoi.\ gi la'o zoi.\ \F{Selcmima.narpanra} \B a .zoi.\ ctaipe lo su'u ro da poi ke'a cmima ja co'e la'o zoi.\ \F{Selcmima.liste} \B a .zoi.\ zo'u li pa nilzilcmi lo'i ro selvau be la'o zoi.\ \F{Selcmima.liste} \B a .zoi.\ poi ke'a du da

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
	\item ga je ko'a selcme lo ro cmima be la'o zoi.\ \F{Jdanunza'omro.cmene} \B a .zoi.\ gi
	\item krici le du'u\ldots
	\begin{itemize}
		\item ga je ga jo la'o zoi.\ \B s .zoi.\ selvau la'o zoi.\ \F{Selcmima.liste} \OpF \$ \F{Jdanunza'omro.velski} \B a .zoi.\ gi la'o zoi.\ \B s .zoi.\ jetnu je cu velski ko'a gi
		\item ko'a jdanunza'omro lo ro prenu poi ke'a zukte lo cmima be la'o zoi.\ \F{Selcmima.liste} \OpF \$ \F{Jdanunza'omro.krinu} \B a .zoi.
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
ni'o ga naja la'oi .\F{f}.\ ctaipe la'oi .\F{Marde}.\ gi la'o zoi.\ \F f \B x\ .zoi.\ ni la'oi .\B{x}.\ vrude la'oi .\F{f}.

\begin{code}
Marde : Set
Marde = Fasnu → ℚ
\end{code}

\subsection{le me'oi .\AgdaKeyword{instance}.}

\begin{code}
postulate instance eqMarde : Eq Marde
\end{code}

\section{la'oi .\AgdaRecord{Prenu}.}
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

\section{la'oi .\AgdaRecord{Lijda}.}
ni'o ga jo ko'a goi la'o zoi.\ \B a .zoi.\ ctaipe la'oi .\AgdaRecord{Lijda}.\ gi\ldots
\begin{itemize}
	\item ga je la'o zoi.\ \F{Lijda.marde} .zoi.\ marde lo seljda be ko'a gi
	\item ga je ga jonai ga je su'o da zo'u da jdanunza'omro fi ko'a gi ko'e goi la'o zoi.\ \F{mapₘ} \F{Selcmima.liste} \OpF \$ Lijda.jdanunza'omro \B a .zoi.\ me'oi .\F{just}.\ lo'i jdanunza'omro be fi ko'a gi ko'e du la'oi .\F{nothing}.\ gi
	\item ga jonai\ldots
	\begin{itemize}
		\item la'oi .\F{nothing}.\ du ko'e goi la'o zoi.\ \F{mapₘ} \Sym(\F{proj₁} \OpF ∘ \F{proj₁}\Sym) \OpF \$ \F{Lijda.cevni} \B a .zoi.\ gi
		\item ga je lo ro seljda be ko'a cu selcei gi\ldots
		\begin{itemize}
			\item ga je ko'e me'oi .\F{just}.\ lo'i cevni ja co'e be ko'a gi
			\item ga jo la'o zoi.\ \B t\ .zoi.\ ctaipe la'o zoi.\ \F{Is-just} \OpF \$ \F{Lijda.cevni} \B a\ .zoi.\ gi ga jo la'o zoi.\ \B Z\ .zoi.\ du la'o zoi.\ \F{Data.Maybe.to-witness} \B t\ .zoi.\ gi la'o zoi.\ \Sym(proj₂ \B Z\Sym) \B m \B n\ .zoi.\ co'e ja ni la'o zoi.\ \F{proj₁} \OpF \Sym(\F{proj₁} \OpF \$ \B Z\Sym) \OpF !\ \B m .zoi.\ nelci la'o zoi.\ \F{proj₁} \OpF \Sym(\F{proj₁} \OpF \$ \B Z\Sym) \OpF !\ \B n .zoi.
		\end{itemize}
	\end{itemize}
\end{itemize}

% ni'o xu cadga fa lo nu la .varik. cu ciksi lo co'e ja ctaipe be le su'u pilno la'o zoi. UL $ List Prenu .zoi. jenai la'o zoi. Selcmima Prenu .zoi.

\begin{code}
record Lijda : Set
  where
  private
    𝔽L : ∀ {a} → {A : Set a}
       → ⦃ Q : LL A ⦄ → ⦃ _ : Eq $ LL.e Q ⦄
       → UL A → Set
    𝔽L = Fin ∘ length ∘ proj₁
  field
    cevni : Maybe $ Σ (UL $ List Prenu) $ (λ X → X → X → ℚ) ∘ 𝔽L
    marde : Marde
    jdanunza'omro : Maybe $ Selcmima Jdanunza'omro
\end{code}
\end{document}
