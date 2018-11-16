\NeedsTeXFormat{LaTeX2e}
\ProvidesClass{rntz}[2018/03/19]

\DeclareOption{marginums}{\PassOptionsToPackage{\CurrentOption}{rntzsection}}
\DeclareOption{nomarginums}{\PassOptionsToPackage{\CurrentOption}{rntzsection}}
\DeclareOption{ribbons}{\PassOptionsToPackage{\CurrentOption}{rntzsection}}
\DeclareOption{noribbons}{\PassOptionsToPackage{\CurrentOption}{rntzsection}}
\DeclareOption{twocolumn}{\ClassWarning{rntz}{Two-column mode is not supported.}}
\DeclareOption*{\PassOptionsToClass{\CurrentOption}{extarticle}}

% Defaults
\ProcessOptions\relax

%% ---- Basic layout ----
\LoadClass{extarticle}
\RequirePackage{rntztitle}      % document title style
\RequirePackage{rntzsection}    % section header style
\RequirePackage{rntzfootnotes}
\RequirePackage{rntzabstract}
% NB. must load rntzref before rntzthm, because of bad cleveref/amsthm
% interaction.
\RequirePackage{rntzref}        % link and references
\RequirePackage{rntzthm}        % theorem styles
