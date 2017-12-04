\ProvidesClass{psartcl}
\DeclareOption*{\PassOptionsToClass{\CurrentOption}{scrartcl}}
\ProcessOptions\relax

%% koma-script and lab fonts, basic layout
\LoadClass[a4paper]{scrartcl}
%\LoadClass[a4paper,twoside,DIV=9]{scrartcl}

% Use Lucida fonts if possible, fallback to standard otherwise
\IfFileExists{lucimatx.sty}
{\usepackage[scale=0.9]{lucimatx}}
{\usepackage{amssymb}}

\usepackage{geometry} % brute force
\geometry{
  includehead,% (=> head is part of total body)
  ignorefoot,% (=> foot is not part of total body)
  top=30mm,% (top of paper |---| top of total body)
  totalwidth=140mm,% (width of total body)
  totalheight=215mm% (height of total body)
}
\linespread{1.04}
\tolerance=2000
\emergencystretch=20pt
\raggedbottom 

\usepackage[utf8]{inputenc}
\usepackage{amsmath}
\usepackage[amsmath,hyperref,thmmarks]{ntheorem}
\usepackage{mathrsfs}
\usepackage{mathpartir} % Didier Remy's inference rules, best layout
\renewcommand{\TirName}[1]{\text{\small#1}}
\usepackage{hyperref}

\renewcommand{\sectfont}{\color{blue}\sffamily\bfseries}
\renewcommand{\emph}[1]{{\color{blue}\textbf{#1}}}
\newcommand{\N}[1]{\ensuremath{{\color{blue}{#1}}}}
\newcommand{\M}[1]{\ensuremath{\mathrm{#1}}}

%% enumerate and itemize
\usepackage[neveradjust,flushleft]{paralist}
\renewenvironment{enumerate}{\compactenum}{\endcompactenum}
\renewenvironment{itemize}{\compactitem}{\endcompactitem}
\setlength{\pltopsep}{.5ex}
\setlength{\plitemsep}{.5ex}

%% Left indents
\newlength{\baseindent}
\setlength{\baseindent}{1.5em} %1.2em
\setlength{\parindent}{\baseindent}
\setdefaultleftmargin{\baseindent}    % paralist
    {\baseindent}{\baseindent}{\baseindent}
    {\baseindent}{\baseindent}
\setlength{\@mathmargin}{\baseindent} % amsmath
\setlength{\multlinegap}{\baseindent} % amsmath
\newcommand{\nomathmargin}{\setlength{\@mathmargin}{0em}}

%% Theorems
\theoremstyle{plain}
\theoremheaderfont{\color{blue}\rmfamily\bfseries}
\theorembodyfont{\normalfont}
\newtheorem{lemma}{Lemma}
\newtheorem{fact}[lemma]{Fact}
\newtheorem{theorem}[lemma]{Theorem}
\newtheorem{corollary}[lemma]{Corollary}
\newtheorem{conjecture}[lemma]{Conjecture}
\newtheorem{assumption}[lemma]{Assumption}
\newtheorem{definition}[lemma]{Definition}
\newtheorem{exercise}[lemma]{Exercise}
\newtheorem{example}[lemma]{Example}
\theoremstyle{nonumberplain}
\theorembodyfont{\normalfont}
\theoremsymbol{{\color{blue}\ensuremath{_\blacksquare}}}
\newtheorem{proof}{Proof.}

%% Floats
\setcounter{topnumber}{3}
\setcounter{bottomnumber}{0}
\setcounter{totalnumber}{3}
\renewcommand*{\floatpagefraction}{0.7}
\renewcommand{\@makecaption}[2]{\vskip+3mm\centering%
  \textcolor{blue}{#1: #2}}

%% Samepage
\renewenvironment{samepage}{%
  \trivlist\item\relax\minipage{\textwidth}}{%
  \endminipage\endtrivlist}
