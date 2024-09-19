my $core_color = "goldenrod";
my $entrypoint_color = "steelblue1";
my $algorithmic_color = "darkturquoise";
my $syntactic_color = "darkorange";
my $semantic_color = "forestgreen";
my $soundness_color = "goldenrod1";
my $completeness_color = "deeppink3";
my $frontend_color = "darkslategray4";
my $extraction_color = "darkslategray3";
my $others_color = "lightpink";
print "digraph Mcltt {\n";
print "  graph [cluster=true,fontsize=28,label=\"Mcltt\",labeljust=l,labelloc=t,penwidth=5,size=15,splines=true,tooltip=\"\"];\n";
print "  node [fontsize=18,shape=note,style=filled,URL=\"https://beluga-lang.github.io/McLTT/\\N.html\"];\n";
print "  subgraph Algorithmic { label=\"Algorithmic\"; fontcolor=$algorithmic_color; color=$algorithmic_color }\n";
print "  subgraph Core { label=\"Core\"; fontcolor=$core_color; color=$core_color }\n";
print "  subgraph Core { subgraph Core_basic { style=invis; subgraph Core_Syntactic { style=\"\"; label=\"Syntactic\"; fontcolor=$syntactic_color; color=$syntactic_color } } }\n";
print "  subgraph Core { subgraph Core_basic { subgraph Core_Semantic { style=\"\"; label=\"Semantic\"; fontcolor=$semantic_color; color=$semantic_color } } }\n";
print "  subgraph Core { subgraph Core_proof { style=invis; subgraph Core_completeness { subgraph Core_Completeness { style=\"\"; label=\"Completeness\"; fontcolor=$completeness_color; color=$completeness_color } } } }\n";
print "  subgraph Core { subgraph Core_proof { subgraph Core_soundness { subgraph Core_Soundness { style=\"\"; label=\"Soundness\"; fontcolor=$soundness_color; color=$soundness_color } } } }\n";
print "  subgraph Extraction { label=\"Extraction\"; fontcolor=$extraction_color; color=$extraction_color }\n";
print "  subgraph Frontend { label=\"Frontend\"; fontcolor=$frontend_color; color=$frontend_color }\n";
while (<>) {
    if (m/([^\s]*)\.vo.*:(.*)/) {
        my $goal = `realpath $1`;
        $dests_rel = $2 ;
        ($path,$src) = ($goal =~ s/\//\./rg =~ m/.*\.theories\.(.*\.)?([^.]*)\n$/);
        my $goalmodule = "Mcltt.$path$src";
        for my $dest_rel (split(" ", $dests_rel)) {
            my $dest = `realpath $dest_rel`;
            $dest =~ s/\//\./g ;
            print "  \"Mcltt.$1\" -> \"$goalmodule\" [arrowtail=inv,dir=both,penwidth=3,tooltip=\"$goalmodule requires Mcltt.$1\"];\n" if ($dest =~ m/.*\.theories\.(.*)\.vo\n/);
        }
        my $nodeformat = "\"$goalmodule\"[label=\"%s\",tooltip=\"$goalmodule\",fillcolor=%s]";
        if ($path =~ m/Algorithmic\.(.*)/) {
            printf "subgraph Algorithmic { $nodeformat }\n", "$1$src", "$algorithmic_color";
        } elsif ($path =~ m/Syntactic\.(.*)/) {
            printf "subgraph Core { subgraph Core_basic { subgraph Core_Syntactic { $nodeformat } } }\n", "$1$src", "$syntactic_color"
        # } elsif ($goalmodule =~ m/Mcltt\.Core\.Semantic\.Consequences$/) {
        #     printf "subgraph Core { subgraph Core_basic { subgraph Core_Semantic { subgraph Core_Semantic_consequence { cluster=false; rank=sink; $nodeformat} } } }\n", "$1$src", "$semantic_color"
        } elsif ($path =~ m/Semantic\.(.*)/) {
            printf "subgraph Core { subgraph Core_basic { subgraph Core_Semantic { $nodeformat } } }\n", "$1$src", "$semantic_color"
        } elsif ($path =~ m/Soundness\.(.*)/) {
            printf "subgraph Core { subgraph Core_proof { subgraph Core_soundness { subgraph Core_Soundness { $nodeformat } } } }\n", "$1$src", "$soundness_color"
        } elsif ($src =~ m/Soundness$/) {
            # printf "subgraph Core { subgraph Core_proof { subgraph Core_soundness { subgraph soundness { cluster=false; rank=sink; $nodeformat } } } }\n", "$src", "$soundness_color"
            printf "subgraph Core { subgraph Core_proof { subgraph Core_soundness { $nodeformat } } }\n", "$src", "$soundness_color"
        # } elsif ($path =~ m/Completeness\.(Consequences\..*)/) {
        #     printf "subgraph Core { subgraph Core_proof { subgraph Core_completeness { subgraph Core_Completeness { subgraph Core_Completeness_consequences { cluster=false; rank=sink; $nodeformat } } } } }\n", "$1$src", "$completeness_color"
        } elsif ($path =~ m/Completeness\.(.*)/) {
            printf "subgraph Core { subgraph Core_proof { subgraph Core_completeness { subgraph Core_Completeness { $nodeformat } } } }\n", "$1$src", "$completeness_color"
        } elsif ($src =~ m/Completeness$/) {
            # printf "subgraph Core { subgraph Core_proof { subgraph Core_completeness { subgraph completeness { cluster=false; rank=sink; $nodeformat } } } }\n", "$src", "$completeness_color"
            printf "subgraph Core { subgraph Core_proof { subgraph Core_completeness { $nodeformat } } }\n", "$src", "$completeness_color"
        } elsif ($path =~ m/Frontend\.(.*)/) {
            printf "subgraph Frontend { $nodeformat }\n", "$1$src", "$frontend_color"
        } elsif ($src =~ m/Entrypoint$/) {
            printf "subgraph entrypoint { cluster=false; rank=sink; $nodeformat }\n", "$src", "$entrypoint_color"
        } elsif ($path =~ m/Extraction\.(.*)/) {
            printf "subgraph Extraction { $nodeformat }\n", "$1$src", "$extraction_color"
        } elsif ($path =~ m/Core\.(.*)$/) {
            printf "subgraph Core { subgraph Core_basic { $nodeformat } }\n", "$1$src", "$core_color"
        } else {
            printf "subgraph others { cluster=false; rank=source; $nodeformat }\n", "$path$src", "$others_color"
        }
    }
}
print "}\n";
