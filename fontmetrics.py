def font(**kwargs): return kwargs
rm = lambda **kwargs: font(family="rm", **kwargs)
sf = lambda **kwargs: font(family="sf", **kwargs)
tt = lambda **kwargs: font(family="tt", **kwargs)
math = lambda **kwargs: font(family="math", **kwargs)

FONT_INFO = {
    # TODO: newmath option for Alegreya
    "Alegreya": rm(ex=4.52, osf="osf", newmath="charter"),
    "AlegreyaSans": rm(ex=4.58, osf="osf"),
    "Baskervaldx": rm(ex=4.31, opts=["proportional"], osf="osf",
                      newmath="baskervaldx"),
    "charter": rm(ex=4.81, package="XCharter", opts=["sups"], osf="osf"),
    "cochineal": rm(ex=4.26, opts=["p","sups"], osf="osf"),
    # TODO: lower eulervm's x-height to give it some _oomph_ when paired with
    # other fonts?
    "eulervm": math(ex=4.59, scale=("variable", "\\zeu@Scale")),
    "inconsolata": tt(ex=4.56999),

    # libertine and biolinum match pretty well visually but have _slightly_
    # differing x-heights. I'm waffling on whether to pretend biolinum has the
    # same x-height has libertine.
    #
    # Also, the libertineRoman package doesn't take a scaling parameter, and
    # loading both libertine[rm] and biolinum clashes. Argh!
    "libertine": rm(ex=4.29, opts=["p", "mono=false", "rm"], osf="osf"),
    "biolinum": sf(ex=4.31999,
                   #ex=4.29,
                   opts=["p"], osf="osf"),

    # TODO: does librebaskerville support osf?
    "librebaskerville": rm(ex=5.29999, newmath="libertine"),

    # TODO: does newpxtext support osf?
    # TODO: handle custom interactions with fontaxes. see rntzfont.sty.
    #
    # XXX: I've manually adjusted the ex-height here to match Euler's, since
    # from inspection with xheight.pdf, the font metadata x-height seems too
    # large.
    "newpxtext": rm(#ex=4.48999 # font metric data
        ex=4.59 # copied from Euler
    ),

    "PTSerif": rm(ex=5,newmath="utopia"),        # TODO: osf?
    "PTSans": sf(ex=5),         # TODO: osf?

    # These match optically, but have different x-height metrics. Not sure
    # whether to use their metrics or just copy sourceserifpro's x-height.
    #
    # TODO: newmath + sourceserifpro?
    "sourceserifpro": rm(ex=4.75, opts=["semibold","proportional"],
                         newmath='charter'),
    "sourcesanspro": sf(ex=4.86,
                        #ex=4.75,
                        opts=["semibold","proportional"]),
    "sourcecodepro": tt(ex=4.79999,
                        #ex=4.75
    ),
}

NEWMATH_EXES = {
    # Same as the fonts they're based on.
    "libertine": 4.29, "cochineal": 4.26, "baskervaldx": 4.31,
     # different from the fonts they're based on.
    "charter": 4.42, "utopia": 4.42,
    #"utopia": 4.8999, # TODO: double check!
}

# Prints LaTeX code that loads the selected fonts, matching x-heights to the
# first font listed, scaled by the given amount.
#
# TODO: a first pass that notices if libertine & biolinum are both requested and
# rewrites the request.
def generate(*fonts, scale=1, linespread=None):
    assert len(fonts) > 0
    primary = fonts[0]
    assert primary in FONT_INFO
    ex = scale * FONT_INFO[primary]["ex"]  # target x-height
    for font in fonts:
        if font == "newmath":
            print(newmath(primary, ex))
            continue
        print(usefont(font, ex))

    # If a linespread was requested, adjust it relative to the ex-height and
    # print it.
    if linespread is None: return
    COMPUTER_MODERN_EX = 4.3055
    print("\\linespread{%s}" % scale_factor(linespread * ex, COMPUTER_MODERN_EX))

def newmath(font, ex, options=[]):
    mathfont = FONT_INFO[font].get('newmath', font)
    assert font == "newpxtext" or mathfont in NEWMATH_EXES
    if font == "newpxtext":
        scale = scale_factor(ex, FONT_INFO['newpxtext']['ex'])
        return f"\\usepackage[scaled={scale},{','.join(options)}]{{newpxmath}}"
    scale = scale_factor(ex, NEWMATH_EXES[mathfont])
    return f"\\usepackage[{mathfont},scaled={scale},{','.join(options)}]{{newtxmath}}"

def usefont(font, ex, options=[]):
    info = FONT_INFO[font]
    pkg = info.get("package", font)
    opts = info.get("opts", []) + options

    # Scale to target ex-height.
    addendum = ""
    if ex is not None and ex != info["ex"]:
        factor = scale_factor(ex, info['ex'])
        how = info.get("scale", ("option","scaled"))
        method = how[0]
        if method == "option":
            opts = [f"{how[1]}={factor}"] + opts
        elif method == "variable":
            addendum = f"\\makeatletter\\edef{how[1]}{{{factor}}}\\makeatother"
        else:
            raise Exception("unrecognized scaling option")

    return f"\\usepackage[{','.join(opts)}]{{{pkg}}}" + addendum

def scale_factor(target, source):
    # use up to 15 digits of precision, drop trailing zeros.
    return ('%.15f' % (target / source)).rstrip('0')
