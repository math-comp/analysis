my %clusters = ( #         directory => [ Cluster Name, Color, URL ]
    classical                        => [ "Classical", "lightgrey", "" ],
    reals                            => [ "Reals", "lightskyblue",  "" ],
    'experimental_reals'             => [ "ExperimentalReals", "cyan", "" ],

    theories                         => [ "Analysis", "aquamarine", "analysis.%s" ],
    'theories/showcase'              => [ "Analysis", "aquamarine", "analysis.showcase.%s" ],

    'theories/topology_theory'       => [ "Topology", "lightpink",
                                          "analysis.topology_theory.%s" ],

    'theories/homotopy_theory'       => [ "Topology", "lightcoral",
                                          "analysis.homotopy_theory.%s" ],

    'theories/normedtype_theory'     => [ "Normedtype", "lightgreen",
                                          "analysis.normedtype_theory.%s" ],

    'theories/functional_analysis'   => [ "FunctionalAnalysis", "chartreuse",
                                          "analysis.functional_analysis.%s"],

    'theories/measure_theory'        => [ "Measure", "orange",
                                          "analysis.measure_theory.%s" ],

    'theories/real_measure'          => [ "RealMeasure", "coral",
                                          "analysis.real_measure.%s" ],

    'theories/lebesgue_integral_theory'
                                     => [ "LebesgueIntegral", "lightyellow",
                                          "analysis.lebesgue_integral_theory.%s" ],

    'theories/elementary_functions'   => [ "ElementaryFunctions", "plum",
                                          "analysis.elementary_functions.%s"],

    'theories/probability_theory'    => [ "Probability", "gold",
                                          "analysis.probability_theory.%s" ],

    reals_stdlib                     => [ "Reals", "lightskyblue",  "" ],
    analysis_stdlib                  => [ "AnalysisStdlib", "lightpink", "" ],
    'analysis_stdlib/showcase'       => [ "AnalysisStdlib", "lightpink", "" ],
);

print "digraph dependencies {\n";
print "  node [shape = box,style = \"filled,rounded\",colorscheme = paired12];\n";

my %seen;
for my $k (sort keys %clusters) {
    my ($cluster) = @{ $clusters{$k} };
    next if $seen{$cluster}++;

    my $cluster_name = "cluster_".$cluster;
    print qq{  subgraph $cluster_name { label="$cluster" }\n};
}

while (<>) {
    if (m/([^\s]*)\.vo.*:(.*)/) {

        my $dests = $2;

        my ($path,$src)
            = ($1 =~ s/\//\//rg =~ m/^(?:(.*)\/)?([^.]*)$/);

        my $url = "mathcomp.$path.$src.html";

        my ($cluster_label, $color, $urltmpl);

        if (exists $clusters{$path}) {
            ($cluster_label, $color, $urltmpl) = @{ $clusters{$path} };
        }

        if (defined $cluster_label) {

            if ($urltmpl ne "") {
                $url = "mathcomp."
                     . sprintf($urltmpl,$src)
                     . ".html";
            }

            my $fontcolor =
                ($color == 2 || $color == 4 || $color == 10)
                ? "white"
                : "black";

            my $cluster = "cluster_".$cluster_label;
            print qq{
subgraph $cluster {
    "$path/$src"[
        label="$src",
        URL="$url",
        fillcolor=$color
    ]
}
};

        } else {

            my $unknown = $path;
            $unknown =~ s#[^A-Za-z0-9_]#_#g;

        }

        for my $dest (split " ", $dests) {
            print qq{  "$1" -> "$path/$src";\n}
                if $dest =~ /(.*)\.vo/;
        }
    }
}

print "}\n";
