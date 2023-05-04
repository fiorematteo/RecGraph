use recgraph::args_parser;
use recgraph::gap_global_abpoa;
use recgraph::gap_local_poa;
use recgraph::global_abpoa;
use recgraph::local_poa;
use recgraph::pathwise_alignment;
use recgraph::pathwise_alignment_gap;
use recgraph::pathwise_alignment_gap_semi;
use recgraph::pathwise_alignment_recombination;
use recgraph::pathwise_alignment_semiglobal;
use recgraph::pathwise_graph;
use recgraph::pathwise_graph::nodes_displacement_matrix;
use recgraph::qgrams;
use recgraph::score_matrix;
use recgraph::sequences;
use recgraph::utils;

use std::time::SystemTime;

#[cfg(not(target_env = "msvc"))]
use tikv_jemallocator::Jemalloc;

#[cfg(not(target_env = "msvc"))]
#[global_allocator]
static GLOBAL: Jemalloc = Jemalloc;

fn main() {
    env_logger::builder()
        .format_target(false)
        .format_module_path(true)
        .init();

    let now = SystemTime::now();

    //get q lenght
    let qgrams_len = args_parser::get_qgrams_lenght();

    // get sequence
    let (sequences, seq_names) = sequences::get_sequences(args_parser::get_sequence_path());

    //get graph
    let graph_path = args_parser::get_graph_path();
    // let graph_struct = graph::read_graph(&graph_path, false);

    //get score matrix
    let score_matrix = score_matrix::create_score_matrix();
    let scores_f32 = score_matrix::create_f32_scores_matrix();

    //get alignment option
    let align_mode = args_parser::get_align_mode();
    let amb_strand = args_parser::get_amb_strand_mode();
    let (b, f) = args_parser::get_b_f();

    //optimize graph
    let mut graph_optimizer = qgrams::get_optimizer(&graph_path, qgrams_len);

    match align_mode {
        //global alignment
        0 => {
            for (i, seq) in sequences.iter().enumerate() {
                let (graph_struct, hofp_forward, hofp_reverse) =
                    graph_optimizer.generate_sequence_graph(seq);

                let r_values = utils::set_r_values(
                    &graph_struct.nwp,
                    &graph_struct.pred_hash,
                    graph_struct.lnz.len(),
                );
                let bases_to_add = (b + f * seq.len() as f32) as usize;
                let alignment = if is_x86_feature_detected!("avx2") {
                    unsafe {
                        global_abpoa::exec_simd(
                            seq,
                            (&seq_names[i], i + 1),
                            &graph_struct,
                            &scores_f32,
                            bases_to_add,
                            false,
                            &hofp_forward,
                            &r_values,
                        )
                    }
                } else {
                    global_abpoa::exec(
                        seq,
                        (&seq_names[i], i + 1),
                        &graph_struct,
                        &score_matrix,
                        bases_to_add,
                        false,
                        &hofp_forward,
                    )
                };
                if amb_strand && alignment.0 < 0 {
                    let rev_seq = sequences::rev_and_compl(seq);
                    let rev_alignment = global_abpoa::exec(
                        &rev_seq,
                        (&seq_names[i], i + 1),
                        &graph_struct,
                        &score_matrix,
                        bases_to_add,
                        true,
                        &hofp_reverse,
                    );
                    if rev_alignment.0 > alignment.0 {
                        utils::write_gaf(&rev_alignment.1.unwrap().to_string(), i + 1);
                    } else {
                        utils::write_gaf(&alignment.1.unwrap().to_string(), i + 1);
                    }
                } else {
                    utils::write_gaf(&alignment.1.unwrap().to_string(), i + 1);
                }
            }
        }
        //local alignment
        1 => {
            for (i, seq) in sequences.iter().enumerate() {
                let (graph_struct, hofp_forward, hofp_reverse) =
                    graph_optimizer.generate_sequence_graph(seq);
                let alignment = if is_x86_feature_detected!("avx2") {
                    unsafe {
                        let temp_score = local_poa::exec_simd(
                            seq,
                            (&seq_names[i], i + 1),
                            &graph_struct,
                            &scores_f32,
                            false,
                            &hofp_forward,
                        );
                        (temp_score.0 as i32, temp_score.1)
                    }
                } else {
                    local_poa::exec(
                        seq,
                        (&seq_names[i], i + 1),
                        &graph_struct,
                        &score_matrix,
                        false,
                        &hofp_forward,
                    )
                };
                if amb_strand {
                    let rev_seq = sequences::rev_and_compl(seq);
                    let alignment_rev = if is_x86_feature_detected!("avx2") {
                        unsafe {
                            let temp_alignment = local_poa::exec_simd(
                                &rev_seq,
                                (&seq_names[i], i + 1),
                                &graph_struct,
                                &scores_f32,
                                true,
                                &hofp_reverse,
                            );
                            (temp_alignment.0 as i32, temp_alignment.1)
                        }
                    } else {
                        local_poa::exec(
                            &rev_seq,
                            (&seq_names[i], i + 1),
                            &graph_struct,
                            &score_matrix,
                            true,
                            &hofp_reverse,
                        )
                    };
                    if alignment.0 < alignment_rev.0 {
                        utils::write_gaf(&alignment.1.unwrap().to_string(), i + 1);
                    } else {
                        utils::write_gaf(&alignment_rev.1.unwrap().to_string(), i + 1);
                    }
                } else {
                    utils::write_gaf(&alignment.1.unwrap().to_string(), i + 1);
                }
            }
        }
        //affine gap global alignment
        2 => {
            let (g_open, g_ext) = args_parser::get_gap_open_gap_ext();

            for (i, seq) in sequences.iter().enumerate() {
                let (graph_struct, hofp_forward, hofp_reverse) =
                    graph_optimizer.generate_sequence_graph(seq);
                let bases_to_add = (b + f * seq.len() as f32) as usize;
                let alignment = gap_global_abpoa::exec(
                    seq,
                    (&seq_names[i], i + 1),
                    &graph_struct,
                    &score_matrix,
                    g_open,
                    g_ext,
                    bases_to_add,
                    false,
                    &hofp_forward,
                );

                if amb_strand && alignment.0 < 0 {
                    let rev_seq = sequences::rev_and_compl(seq);
                    let rev_alignment = gap_global_abpoa::exec(
                        &rev_seq,
                        (&seq_names[i], i + 1),
                        &graph_struct,
                        &score_matrix,
                        g_open,
                        g_ext,
                        bases_to_add,
                        true,
                        &hofp_reverse,
                    );
                    if rev_alignment.0 > alignment.0 {
                        utils::write_gaf(&rev_alignment.1.unwrap().to_string(), i + 1);
                    } else {
                        utils::write_gaf(&alignment.1.unwrap().to_string(), i + 1);
                    }
                } else {
                    utils::write_gaf(&alignment.1.unwrap().to_string(), i + 1);
                }
            }
        }
        //affine gap local alignment
        3 => {
            let (g_open, g_ext) = args_parser::get_gap_open_gap_ext();
            for (i, seq) in sequences.iter().enumerate() {
                let (graph_struct, hofp_forward, hofp_reverse) =
                    graph_optimizer.generate_sequence_graph(seq);
                let alignment = gap_local_poa::exec(
                    seq,
                    (&seq_names[i], i + 1),
                    &graph_struct,
                    &score_matrix,
                    g_open,
                    g_ext,
                    false,
                    &hofp_forward,
                );
                if amb_strand {
                    let rev_seq = sequences::rev_and_compl(seq);
                    let rev_alignment = gap_local_poa::exec(
                        &rev_seq,
                        (&seq_names[i], i + 1),
                        &graph_struct,
                        &score_matrix,
                        g_open,
                        g_ext,
                        false,
                        &hofp_reverse,
                    );
                    if rev_alignment.0 > alignment.0 {
                        utils::write_gaf(&rev_alignment.1.unwrap().to_string(), i + 1);
                    } else {
                        utils::write_gaf(&alignment.1.unwrap().to_string(), i + 1);
                    }
                } else {
                    utils::write_gaf(&alignment.1.unwrap().to_string(), i + 1);
                }
            }
        }
        4 => {
            for (i, seq) in sequences.iter().enumerate() {
                let graph = graph_optimizer.generate_variation_graph(seq, false);
                let mut gaf = pathwise_alignment::exec(seq, &graph, &score_matrix);
                gaf.query_name = seq_names[i].clone();
                utils::write_gaf(&gaf.to_string(), i);
            }
        }
        5 => {
            for (i, seq) in sequences.iter().enumerate() {
                let graph = graph_optimizer.generate_variation_graph(seq, false);
                let mut gaf = pathwise_alignment_semiglobal::exec(seq, &graph, &score_matrix);
                gaf.query_name = seq_names[i].clone();
                utils::write_gaf(&gaf.to_string(), i);
            }
        }
        6 => {
            let (g_open, g_ext) = args_parser::get_gap_open_gap_ext();
            for (i, seq) in sequences.iter().enumerate() {
                let graph = graph_optimizer.generate_variation_graph(seq, false);
                let best_path =
                    pathwise_alignment_gap::exec(seq, &graph, &score_matrix, g_open, g_ext);
                println!("Best path sequence {i}: {best_path}");
            }
        }
        7 => {
            let (g_open, g_ext) = args_parser::get_gap_open_gap_ext();
            for (i, seq) in sequences.iter().enumerate() {
                let graph = graph_optimizer.generate_variation_graph(seq, false);
                let best_path =
                    pathwise_alignment_gap_semi::exec(seq, &graph, &score_matrix, g_open, g_ext);
                println!("Best path sequence {i}: {best_path}");
            }
        }
        8 | 9 => {
            let (base_rec_cost, multi_rec_cost) = args_parser::get_base_multi_recombination_cost();
            let rbw = args_parser::get_recombination_band_width();
            for (i, seq) in sequences.iter().enumerate() {
                let graph = graph_optimizer.generate_variation_graph(seq, false);
                let rev_graph = pathwise_graph::create_reverse_path_graph(&graph);
                let displ_matrix = nodes_displacement_matrix(&graph, &rev_graph);
                let mut gaf = pathwise_alignment_recombination::exec(
                    align_mode,
                    seq,
                    &graph,
                    &rev_graph,
                    &score_matrix,
                    base_rec_cost,
                    multi_rec_cost,
                    &displ_matrix,
                    rbw,
                );
                gaf.query_name = seq_names[i].clone();

                utils::write_gaf(&gaf.to_string(), i);
            }
        }

        _ => {
            panic!("Alignment mode must be in [0..9]");
        }
    }
    match now.elapsed() {
        Ok(elapsed) => {
            // it prints '2'
            eprintln!("Done in {}.", elapsed.as_secs());
        }
        Err(e) => {
            // an error occurred!
            eprintln!("Error: {e:?}");
        }
    }
}

#[cfg(test)]
mod tests {
    use std::process::{Child, Command, Stdio};

    fn launch_command_with_mode(mode: usize) -> Child {
        Command::new("target/release/recgraph")
            .args(&[
                &format!("-m{}", mode),
                "example/reads.fa",
                "example/graph.gfa",
                "--out_file",
                "/dev/null",
                "-q20",
            ])
            .stdout(Stdio::null())
            .stderr(Stdio::null())
            .spawn()
            .unwrap()
    }

    #[test]
    fn full_integration() {
        Command::new("cargo")
            .args(&["build", "--release"])
            .output()
            .unwrap();
        let childs = (0..=9)
            .map(|mode| launch_command_with_mode(mode))
            .collect::<Vec<_>>();
        childs.into_iter().for_each(|mut child| {
            assert!(child.wait().map_or(false, |r| r.success()));
        });
    }
}
