my %clusters = ( #         directory => [ Cluster Name, Color, URL ]
    classical                        => [ "Classical", 1, "" ],
    'experimental_reals'             => [ "ExperimentalReals", 1, "" ],
    reals                            => [ "Reals", 2,  "" ],
    reals_stdlib                     => [ "Reals", 2,  "" ],
    analysis_stdlib                  => [ "AnalysisStdlib", 5, "" ],
    'analysis_stdlib/showcase'       => [ "AnalysisStdlib", 5, "" ],
    theories                         => [ "Analysis", 5, "analysis.%s" ],
    'theories/showcase'              => [ "Analysis", 5, "analysis.showcase.%s" ],

    'theories/topology_theory'       => [ "Topology", 4,
                                          "analysis.topology_theory.%s" ],
    'theories/homotopy_theory'       => [ "Topology", 4,
                                          "analysis.homotopy_theory.%s" ],

    'theories/normedtype_theory'     => [ "Normedtype", 9,
                                          "analysis.normedtype_theory.%s" ],

    'theories/lebesgue_integral_theory'
                                     => [ "LebesgueIntegral", 10,
                                          "analysis.lebesgue_integral_theory.%s" ],

    'theories/measure_theory'        => [ "Measure", 11,
                                          "analysis.measure_theory.%s" ],

    'theories/probability_theory'    => [ "Probability", 12,
                                          "analysis.probability_theory.%s" ],

    'theories/functional_analysis'   => [ "FunctionalAnalysis", 3,
                                          "analysis.functional_analysis.%s"],
);

print "digraph dependencies {\n";
print "  node [shape = ellipse,style=filled,colorscheme = paired12];\n";

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
