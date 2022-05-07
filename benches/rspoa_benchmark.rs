use std::collections::HashMap;

use criterion::{black_box, criterion_group, criterion_main, Criterion};
use rspoa::{gap_local_poa, gap_mk_abpoa, global_mk_abpoa, graph, local_poa, matrix};

fn global_abpoa_benchmark(c: &mut Criterion) {
    let seq = "TGATATAAAGAAATGAGATTTATTGCCTTGTGGGGGGAAGGGATGTGGTTGTGATAGGCAGGCCACTCTGGGATCCCTGGGATGCAAGCCCAGGGACAGCAGAGTCCCCAGGTGGGAAATCTACACACACACCCCAGGGATGTCCCAGAGACTTCTACCCTAAGAGGAGATCCTGGGCAGGATGTGAGAAATCTGAGCATCCTCTGTTTGGATGGCCGAAGCTGCTGGCATCAAACTCTGGTCTGGAAGAATCAGTCTGGGGGAGAGACAGGGATGGAGGAAAGGCATCAGGGGATCCATCCTCCTCCTCCTTCTCCTCCTCCTCCTCCCCCACAAAGGCCTTGCTCGCCCTGCCTGCACCACACCCTGCAGAAGTTGATCTCTCCTTGTTCCCAAATCATCTCCAAGCACCCTTCCTACAGCACCCCATGATTCCTTTTTTCACTCAAAGCAATTCTTGTGACCCATAACTGTGTGTGTGTAACTGGGTCCCCAACTGGGAAGATGTGCCCCCATGGTGCTGGATACAGGCCCCCACACCCAAGGGCCTGAGGATCGCTATATGTCCCCCCATGCCACAAAATAATCCTGACACATGCACGCATGCACCACTGTATCTGGCTCCCACAGGCTCACCCGCCCCCTCCAGATGACATACCACCTGAGCAAGGCTTCCGGAAGTAGATGATGAGAACAATGCCCACGATGATGCCCAGCACACCCAGGCCAAAGGCCACGCCACACAGCACATTCTCCAGCAGATCTGAGGGCAGTGCGTTCCGGGGTACTGGAGGAAATGAGTGGCTCAGCCTGGGGACCTAGTTAGGGAGCCTCCCACCCAGGGAAATGACGTGGGTGTCTGGGATGACATGGGAGACTGGGATGGGCTTAGGGTAGGAATGGACTAAACAAGGTACCAGTGGAGAAAGAAGCCTCCTCCCATGGATCTATCCCTTTTTGCCCCCAAAAGGACCAGAATTCCAGGGAGAAAGCCTCACCCCAATAGGCAATTGCTGTGTAGCGGTCAATTTCGTGAGTCACAATGCAGGAGAAAATGTCAGAAGGTTCTGGTGTGAAGTTTAAGTAAGAAAAGGCCTGGAAGCTGAGTCCATCGACAGCTGAGACAAAAGTAGGCCCAAATCCTTCCACAGGGACGGAATGATGCTGCCAGTTCACTGTCAGCATGGGTGGGAAGAGATTACTGACAAAACAGACCAAAGTGTTGGGCTTGCCAAACTCCAGGGGCTTCAGCGTGAACACTTCAGCGATAGGAAACCCTGGTGGGGGGATTGAAGTGTAGGGGGAAAAAGAGACTAGTTTAGATGGTATCTCTGTGTTTGGAGGGGCCATGGCATATGGAGGGGAGGGCAGAGAAGAACACAGTGGGTCAGGCTTTGGGAGACAGAGATGAGCGAGGAGCTGGGCTCTGAAGGGAGGTCTTCTTCCAGGCAAGGACTGCAGCTAGACATAGAAGCAGAGCCAGATCCAGGCTACTCTGGACCCCTCCACCATGACTTCCTTCAGCACTTCCTGTCTAGAGCTCACATTGATGTCTAACCATGCACTGTCTTCTCACTAAGACATAGTCACGTCATCAGATATTTCCACTCTTCCCATCCATCTTGCTGGGCATAGTAGCACAAGTGTTAATATTCAGTAGGTATCAGTTGGTACCTGTTGAATTCATCACATTCAATACATAGTTCTGAATGCCTACTACATGCTAGGTACTTCGGCCCACCAAAAGAACACAGGGTGCAGACCAAGGCTGGTGGAAAAATTAAGGTGATGAAGAGAACCAGAAAGTATTTGAGATGGGGAGCTGGTATCAAGGGGAATTATTCAGTGTACAGATCAATGAGGTTAATGCAGCCCTCCTCCCTTCACTCCCCAGAAAACTCCTGACCTCTGGACACCGGGATTTTCCCATCAAGTTTTGGCCCTATTTGCTGGATCATCCACTCGCAGAACTCTTTGTCAAATAAAATGGCAGGAGCATCTCCCTGTTCCTGAGCCCAGTCAGCAAATTCGGGCAGGCGAGGCACCCGAGTGTTCTGGGAAAAGTCGAAGAAGAAAAGCTGGTCCTCGTCGTAGGCCTCAGAGAGTCCCACACTGGGACTCCCATCCTGGCAGTACACTGTGTGCAGGAATGTGTGGTTTTGCAGGTCATCTGGCCACATTGGAGTAGGAGCTGCAAAGGACACAGGGTGAGGTTCAGGGAGGTGGGAGCCTTCTCCTCCAACTTAAAAAACAGCAAGGTGGGGCTAGGCGCAGTGGCTCATGCCTGTAATCCCAGCACTTTGGGAGGCCAAGGTGGGTGGATCATGAGGTCAGGAGTTTGAGACCAGCCTGGCCAGCATGGTGAAACTCCGTCTCTACTAAAAATACAAAAAAGTAGCTGGGCATGTTGGCATGCGCCTGTAGCTACTCGGGAGGCTGAGGGAGGAGAATTGCTTGAACCAGGGAGGCAGAGGTTGCCGGGAGCTAAGATTAAGCCACTGCACTCCAGCCTGGGTGACAGAGTGAGACTCTGTCTCAAAACAAAACAACAAAAACAAGCAAGGCCTGCTTAAGGAGCGTGGGCTGAGGTGAGACCCTTTCCTGTGTCTGTTATTTAGACTCCCCCTCCCAAAGGGGGTGAAGAACAAATTATGGCATCTCTCCAAGCTTCCCCTGCCTATAAAAAGGCCAGTTGGCAAAAGTAAAGAGTTCTACTTTCTAAAGTGACAGATTCAGGCCAGGCATGGTGGCTCATGCCTGTAATCCCAGCACTTTGGGAGGCTGAGGCAGGCAGATTGCTTGAGCCCAGGAGTTCAAGACCAACCTGGGCAACACAGCGAGACCCTGTCTCTACAAAAAATACAAAAACTTAGCCAGGTGTGGTGGCAAACACCTGTGGTCTCAGCTACTCTGGAGGCTGAGGCAGGAGGATTGCTTGTGCCTAGGAAGTTGGGGCTGCAGTGAGCCATGATTGTGCCACTGGACTCCAGCCCAGGTGACAGAATGAGCCCGTCTCAAAAAATATATATATAAAGGCCGGGCGCGGTGGCTCAAGCTTGTAATCCCAGCACTTTGGGAGGCCAAGGCGGGTGGATCACCTGAGGTCAGGAGTTTGAGACCAGCCTGGCAAACATGATGAAACCCCATCTCTACTAAAAATACAAAAATCAGCTGGGTGTGGTGGCATGCGCCTGTAATCCCAGCTACTTGGGAGGCTGAGGCAGGAGAGTCTCTTGAACCCCAGAGGCAGGGGTTGCAGGGAGCCGAGATCACGTCACTGCACTCTACCCTGGGTGACAGAGCGAGATGCCGTGTCAAAAAAAATAAATTAAATCAAATAAAAAATTTAAAAATGTATATATATAAAATAAAGTGACAGATTCAGAGTCACTGTTCATTGTGTGTTTGGGGGCTGCACAAAGACACCTAGCCAAAGAAGCAAGTGAAAGCCTGCATTCTGCTCACCATGCCATACATCCTGGCATAGGGCTGTATCCTCCCAAAGGGGATTCCTTTGTCTAATTCATACCAGGCCACTGTATTGACTAGAGAAGGCCATGGATGGGTTTCTCACTCTTAGAAGGGAAAGAGGAGGAATGGCTACAGCCTCCCCAAGCCATAGATGGGACTGCCTCCCACTATCCCCAGACACAAATGGTAAATTGGAAAACCTGTATCCAGACATTTCTTCAGCCACTTCATTGGCACCAAGCGTCTCTCAAAATGTCTTCTGTTCCTTAACCTACCAGGCCTCCCAAAGACAGCAATGGGAGAAGTGACCCCATAACTGCATAAAATAATCCCTCTTCTTTGAAGCTCTTGGCAGGAATCGCTCAGCCAGCAGGAAACCTTTAACCCAATACCCAGAAAAACAGACATTTGGAGGAAGAGGGATCTTCCAGATTATTCTTCCATTCTGCCCCATCCTCTACAGAGAAGGAAACTAAGACACTTTTCAAGAATCACAAGATAAGTTAATGATAGAAAGCAGAGTAGAATCTTGAGTGGAGGAGTGAAAATAACATTCACTTTGTTCAAATCCCAGCTCTACCACTTTCCAATGGTGTGAACTTGCACAAATAACTCTGAGTCTCATTTTCTTCATTTGTAAAATGGAGAGAACAATCTCCGCTTCAAGAGATTGTCTTAAATGGAACATGCAAAGCATCACTGATATCGTTTACCAACCACACATAGCAGCTGTCTTTCCCCACTCCCCTGTTGTTTCCACTGCCTCATAAGACTTCCCACCACTCACAAAGCACAGCGCTTTTCCTCACAAAGCTGAGTGGGCTCCCTAGGTTCAGGATGGAAGTAAATAGGAGTACCATCTTACCTTCAGGGACGGCCCAGGAGTGGGGTAGCAGCCACAGAAGTGGTAACATCTGTAGCAGCGCAGCTCCTTGGTTCTGTTCATGACCCATACCTTCTTGCCACACAGTAGGTAGGAGCTACCAACCCAGCCAACCCAGCTTCCCCAACTCCCTCCCCGAGAGGGTGGCCTTAGAT";
    let mut sequence = seq.chars().collect::<Vec<char>>();
    sequence.insert(0, '$');

    let graph_struct = graph::read_graph(
        &"tests/DMA-3108.fa.353ea42.34ee7b1.1576367.smooth.fix.gfa",
        false,
    );

    let score_matrix = matrix::create_score_matrix_match_mis(2, -4);

    let (b, f) = (1.0, 0.3);
    let bta = (b + f * sequence.len() as f32) as usize;

    c.bench_function("global_abpoa", |b| {
        b.iter(|| {
            global_mk_abpoa::exec(
                black_box(&sequence),
                ("bench_sequence", 0),
                black_box(&graph_struct),
                black_box(&score_matrix),
                bta,
                false,
                &HashMap::new(),
            )
        })
    });
}

fn local_poa_benchmark(c: &mut Criterion) {
    let seq = "TGATATAAAGAAATGAGATTTATTGCCTTGTGGGGGGAAGGGATGTGGTTGTGATAGGCAGGCCACTCTGGGATCCCTGGGATGCAAGCCCAGGGACAGCAGAGTCCCCAGGTGGGAAATCTACACACACACCCCAGGGATGTCCCAGAGACTTCTACCCTAAGAGGAGATCCTGGGCAGGATGTGAGAAATCTGAGCATCCTCTGTTTGGATGGCCGAAGCTGCTGGCATCAAACTCTGGTCTGGAAGAATCAGTCTGGGGGAGAGACAGGGATGGAGGAAAGGCATCAGGGGATCCATCCTCCTCCTCCTTCTCCTCCTCCTCCTCCCCCACAAAGGCCTTGCTCGCCCTGCCTGCACCACACCCTGCAGAAGTTGATCTCTCCTTGTTCCCAAATCATCTCCAAGCACCCTTCCTACAGCACCCCATGATTCCTTTTTTCACTCAAAGCAATTCTTGTGACCCATAACTGTGTGTGTGTAACTGGGTCCCCAACTGGGAAGATGTGCCCCCATGGTGCTGGATACAGGCCCCCACACCCAAGGGCCTGAGGATCGCTATATGTCCCCCCATGCCACAAAATAATCCTGACACATGCACGCATGCACCACTGTATCTGGCTCCCACAGGCTCACCCGCCCCCTCCAGATGACATACCACCTGAGCAAGGCTTCCGGAAGTAGATGATGAGAACAATGCCCACGATGATGCCCAGCACACCCAGGCCAAAGGCCACGCCACACAGCACATTCTCCAGCAGATCTGAGGGCAGTGCGTTCCGGGGTACTGGAGGAAATGAGTGGCTCAGCCTGGGGACCTAGTTAGGGAGCCTCCCACCCAGGGAAATGACGTGGGTGTCTGGGATGACATGGGAGACTGGGATGGGCTTAGGGTAGGAATGGACTAAACAAGGTACCAGTGGAGAAAGAAGCCTCCTCCCATGGATCTATCCCTTTTTGCCCCCAAAAGGACCAGAATTCCAGGGAGAAAGCCTCACCCCAATAGGCAATTGCTGTGTAGCGGTCAATTTCGTGAGTCACAATGCAGGAGAAAATGTCAGAAGGTTCTGGTGTGAAGTTTAAGTAAGAAAAGGCCTGGAAGCTGAGTCCATCGACAGCTGAGACAAAAGTAGGCCCAAATCCTTCCACAGGGACGGAATGATGCTGCCAGTTCACTGTCAGCATGGGTGGGAAGAGATTACTGACAAAACAGACCAAAGTGTTGGGCTTGCCAAACTCCAGGGGCTTCAGCGTGAACACTTCAGCGATAGGAAACCCTGGTGGGGGGATTGAAGTGTAGGGGGAAAAAGAGACTAGTTTAGATGGTATCTCTGTGTTTGGAGGGGCCATGGCATATGGAGGGGAGGGCAGAGAAGAACACAGTGGGTCAGGCTTTGGGAGACAGAGATGAGCGAGGAGCTGGGCTCTGAAGGGAGGTCTTCTTCCAGGCAAGGACTGCAGCTAGACATAGAAGCAGAGCCAGATCCAGGCTACTCTGGACCCCTCCACCATGACTTCCTTCAGCACTTCCTGTCTAGAGCTCACATTGATGTCTAACCATGCACTGTCTTCTCACTAAGACATAGTCACGTCATCAGATATTTCCACTCTTCCCATCCATCTTGCTGGGCATAGTAGCACAAGTGTTAATATTCAGTAGGTATCAGTTGGTACCTGTTGAATTCATCACATTCAATACATAGTTCTGAATGCCTACTACATGCTAGGTACTTCGGCCCACCAAAAGAACACAGGGTGCAGACCAAGGCTGGTGGAAAAATTAAGGTGATGAAGAGAACCAGAAAGTATTTGAGATGGGGAGCTGGTATCAAGGGGAATTATTCAGTGTACAGATCAATGAGGTTAATGCAGCCCTCCTCCCTTCACTCCCCAGAAAACTCCTGACCTCTGGACACCGGGATTTTCCCATCAAGTTTTGGCCCTATTTGCTGGATCATCCACTCGCAGAACTCTTTGTCAAATAAAATGGCAGGAGCATCTCCCTGTTCCTGAGCCCAGTCAGCAAATTCGGGCAGGCGAGGCACCCGAGTGTTCTGGGAAAAGTCGAAGAAGAAAAGCTGGTCCTCGTCGTAGGCCTCAGAGAGTCCCACACTGGGACTCCCATCCTGGCAGTACACTGTGTGCAGGAATGTGTGGTTTTGCAGGTCATCTGGCCACATTGGAGTAGGAGCTGCAAAGGACACAGGGTGAGGTTCAGGGAGGTGGGAGCCTTCTCCTCCAACTTAAAAAACAGCAAGGTGGGGCTAGGCGCAGTGGCTCATGCCTGTAATCCCAGCACTTTGGGAGGCCAAGGTGGGTGGATCATGAGGTCAGGAGTTTGAGACCAGCCTGGCCAGCATGGTGAAACTCCGTCTCTACTAAAAATACAAAAAAGTAGCTGGGCATGTTGGCATGCGCCTGTAGCTACTCGGGAGGCTGAGGGAGGAGAATTGCTTGAACCAGGGAGGCAGAGGTTGCCGGGAGCTAAGATTAAGCCACTGCACTCCAGCCTGGGTGACAGAGTGAGACTCTGTCTCAAAACAAAACAACAAAAACAAGCAAGGCCTGCTTAAGGAGCGTGGGCTGAGGTGAGACCCTTTCCTGTGTCTGTTATTTAGACTCCCCCTCCCAAAGGGGGTGAAGAACAAATTATGGCATCTCTCCAAGCTTCCCCTGCCTATAAAAAGGCCAGTTGGCAAAAGTAAAGAGTTCTACTTTCTAAAGTGACAGATTCAGGCCAGGCATGGTGGCTCATGCCTGTAATCCCAGCACTTTGGGAGGCTGAGGCAGGCAGATTGCTTGAGCCCAGGAGTTCAAGACCAACCTGGGCAACACAGCGAGACCCTGTCTCTACAAAAAATACAAAAACTTAGCCAGGTGTGGTGGCAAACACCTGTGGTCTCAGCTACTCTGGAGGCTGAGGCAGGAGGATTGCTTGTGCCTAGGAAGTTGGGGCTGCAGTGAGCCATGATTGTGCCACTGGACTCCAGCCCAGGTGACAGAATGAGCCCGTCTCAAAAAATATATATATAAAGGCCGGGCGCGGTGGCTCAAGCTTGTAATCCCAGCACTTTGGGAGGCCAAGGCGGGTGGATCACCTGAGGTCAGGAGTTTGAGACCAGCCTGGCAAACATGATGAAACCCCATCTCTACTAAAAATACAAAAATCAGCTGGGTGTGGTGGCATGCGCCTGTAATCCCAGCTACTTGGGAGGCTGAGGCAGGAGAGTCTCTTGAACCCCAGAGGCAGGGGTTGCAGGGAGCCGAGATCACGTCACTGCACTCTACCCTGGGTGACAGAGCGAGATGCCGTGTCAAAAAAAATAAATTAAATCAAATAAAAAATTTAAAAATGTATATATATAAAATAAAGTGACAGATTCAGAGTCACTGTTCATTGTGTGTTTGGGGGCTGCACAAAGACACCTAGCCAAAGAAGCAAGTGAAAGCCTGCATTCTGCTCACCATGCCATACATCCTGGCATAGGGCTGTATCCTCCCAAAGGGGATTCCTTTGTCTAATTCATACCAGGCCACTGTATTGACTAGAGAAGGCCATGGATGGGTTTCTCACTCTTAGAAGGGAAAGAGGAGGAATGGCTACAGCCTCCCCAAGCCATAGATGGGACTGCCTCCCACTATCCCCAGACACAAATGGTAAATTGGAAAACCTGTATCCAGACATTTCTTCAGCCACTTCATTGGCACCAAGCGTCTCTCAAAATGTCTTCTGTTCCTTAACCTACCAGGCCTCCCAAAGACAGCAATGGGAGAAGTGACCCCATAACTGCATAAAATAATCCCTCTTCTTTGAAGCTCTTGGCAGGAATCGCTCAGCCAGCAGGAAACCTTTAACCCAATACCCAGAAAAACAGACATTTGGAGGAAGAGGGATCTTCCAGATTATTCTTCCATTCTGCCCCATCCTCTACAGAGAAGGAAACTAAGACACTTTTCAAGAATCACAAGATAAGTTAATGATAGAAAGCAGAGTAGAATCTTGAGTGGAGGAGTGAAAATAACATTCACTTTGTTCAAATCCCAGCTCTACCACTTTCCAATGGTGTGAACTTGCACAAATAACTCTGAGTCTCATTTTCTTCATTTGTAAAATGGAGAGAACAATCTCCGCTTCAAGAGATTGTCTTAAATGGAACATGCAAAGCATCACTGATATCGTTTACCAACCACACATAGCAGCTGTCTTTCCCCACTCCCCTGTTGTTTCCACTGCCTCATAAGACTTCCCACCACTCACAAAGCACAGCGCTTTTCCTCACAAAGCTGAGTGGGCTCCCTAGGTTCAGGATGGAAGTAAATAGGAGTACCATCTTACCTTCAGGGACGGCCCAGGAGTGGGGTAGCAGCCACAGAAGTGGTAACATCTGTAGCAGCGCAGCTCCTTGGTTCTGTTCATGACCCATACCTTCTTGCCACACAGTAGGTAGGAGCTACCAACCCAGCCAACCCAGCTTCCCCAACTCCCTCCCCGAGAGGGTGGCCTTAGAT";
    let mut sequence = seq.chars().collect::<Vec<char>>();
    sequence.insert(0, '$');

    let graph_struct = graph::read_graph(
        &"tests/DMA-3108.fa.353ea42.34ee7b1.1576367.smooth.fix.gfa",
        false,
    );

    let score_matrix = matrix::create_score_matrix_match_mis(2, -4);

    c.bench_function("local_abpoa", |b| {
        b.iter(|| {
            local_poa::exec(
                black_box(&sequence),
                ("bench_sequence", 0),
                black_box(&graph_struct),
                black_box(&score_matrix),
                false,
                &HashMap::new(),
            )
        })
    });
}

fn global_gap_abpoa_benchmark(c: &mut Criterion) {
    let seq = "TGATATAAAGAAATGAGATTTATTGCCTTGTGGGGGGAAGGGATGTGGTTGTGATAGGCAGGCCACTCTGGGATCCCTGGGATGCAAGCCCAGGGACAGCAGAGTCCCCAGGTGGGAAATCTACACACACACCCCAGGGATGTCCCAGAGACTTCTACCCTAAGAGGAGATCCTGGGCAGGATGTGAGAAATCTGAGCATCCTCTGTTTGGATGGCCGAAGCTGCTGGCATCAAACTCTGGTCTGGAAGAATCAGTCTGGGGGAGAGACAGGGATGGAGGAAAGGCATCAGGGGATCCATCCTCCTCCTCCTTCTCCTCCTCCTCCTCCCCCACAAAGGCCTTGCTCGCCCTGCCTGCACCACACCCTGCAGAAGTTGATCTCTCCTTGTTCCCAAATCATCTCCAAGCACCCTTCCTACAGCACCCCATGATTCCTTTTTTCACTCAAAGCAATTCTTGTGACCCATAACTGTGTGTGTGTAACTGGGTCCCCAACTGGGAAGATGTGCCCCCATGGTGCTGGATACAGGCCCCCACACCCAAGGGCCTGAGGATCGCTATATGTCCCCCCATGCCACAAAATAATCCTGACACATGCACGCATGCACCACTGTATCTGGCTCCCACAGGCTCACCCGCCCCCTCCAGATGACATACCACCTGAGCAAGGCTTCCGGAAGTAGATGATGAGAACAATGCCCACGATGATGCCCAGCACACCCAGGCCAAAGGCCACGCCACACAGCACATTCTCCAGCAGATCTGAGGGCAGTGCGTTCCGGGGTACTGGAGGAAATGAGTGGCTCAGCCTGGGGACCTAGTTAGGGAGCCTCCCACCCAGGGAAATGACGTGGGTGTCTGGGATGACATGGGAGACTGGGATGGGCTTAGGGTAGGAATGGACTAAACAAGGTACCAGTGGAGAAAGAAGCCTCCTCCCATGGATCTATCCCTTTTTGCCCCCAAAAGGACCAGAATTCCAGGGAGAAAGCCTCACCCCAATAGGCAATTGCTGTGTAGCGGTCAATTTCGTGAGTCACAATGCAGGAGAAAATGTCAGAAGGTTCTGGTGTGAAGTTTAAGTAAGAAAAGGCCTGGAAGCTGAGTCCATCGACAGCTGAGACAAAAGTAGGCCCAAATCCTTCCACAGGGACGGAATGATGCTGCCAGTTCACTGTCAGCATGGGTGGGAAGAGATTACTGACAAAACAGACCAAAGTGTTGGGCTTGCCAAACTCCAGGGGCTTCAGCGTGAACACTTCAGCGATAGGAAACCCTGGTGGGGGGATTGAAGTGTAGGGGGAAAAAGAGACTAGTTTAGATGGTATCTCTGTGTTTGGAGGGGCCATGGCATATGGAGGGGAGGGCAGAGAAGAACACAGTGGGTCAGGCTTTGGGAGACAGAGATGAGCGAGGAGCTGGGCTCTGAAGGGAGGTCTTCTTCCAGGCAAGGACTGCAGCTAGACATAGAAGCAGAGCCAGATCCAGGCTACTCTGGACCCCTCCACCATGACTTCCTTCAGCACTTCCTGTCTAGAGCTCACATTGATGTCTAACCATGCACTGTCTTCTCACTAAGACATAGTCACGTCATCAGATATTTCCACTCTTCCCATCCATCTTGCTGGGCATAGTAGCACAAGTGTTAATATTCAGTAGGTATCAGTTGGTACCTGTTGAATTCATCACATTCAATACATAGTTCTGAATGCCTACTACATGCTAGGTACTTCGGCCCACCAAAAGAACACAGGGTGCAGACCAAGGCTGGTGGAAAAATTAAGGTGATGAAGAGAACCAGAAAGTATTTGAGATGGGGAGCTGGTATCAAGGGGAATTATTCAGTGTACAGATCAATGAGGTTAATGCAGCCCTCCTCCCTTCACTCCCCAGAAAACTCCTGACCTCTGGACACCGGGATTTTCCCATCAAGTTTTGGCCCTATTTGCTGGATCATCCACTCGCAGAACTCTTTGTCAAATAAAATGGCAGGAGCATCTCCCTGTTCCTGAGCCCAGTCAGCAAATTCGGGCAGGCGAGGCACCCGAGTGTTCTGGGAAAAGTCGAAGAAGAAAAGCTGGTCCTCGTCGTAGGCCTCAGAGAGTCCCACACTGGGACTCCCATCCTGGCAGTACACTGTGTGCAGGAATGTGTGGTTTTGCAGGTCATCTGGCCACATTGGAGTAGGAGCTGCAAAGGACACAGGGTGAGGTTCAGGGAGGTGGGAGCCTTCTCCTCCAACTTAAAAAACAGCAAGGTGGGGCTAGGCGCAGTGGCTCATGCCTGTAATCCCAGCACTTTGGGAGGCCAAGGTGGGTGGATCATGAGGTCAGGAGTTTGAGACCAGCCTGGCCAGCATGGTGAAACTCCGTCTCTACTAAAAATACAAAAAAGTAGCTGGGCATGTTGGCATGCGCCTGTAGCTACTCGGGAGGCTGAGGGAGGAGAATTGCTTGAACCAGGGAGGCAGAGGTTGCCGGGAGCTAAGATTAAGCCACTGCACTCCAGCCTGGGTGACAGAGTGAGACTCTGTCTCAAAACAAAACAACAAAAACAAGCAAGGCCTGCTTAAGGAGCGTGGGCTGAGGTGAGACCCTTTCCTGTGTCTGTTATTTAGACTCCCCCTCCCAAAGGGGGTGAAGAACAAATTATGGCATCTCTCCAAGCTTCCCCTGCCTATAAAAAGGCCAGTTGGCAAAAGTAAAGAGTTCTACTTTCTAAAGTGACAGATTCAGGCCAGGCATGGTGGCTCATGCCTGTAATCCCAGCACTTTGGGAGGCTGAGGCAGGCAGATTGCTTGAGCCCAGGAGTTCAAGACCAACCTGGGCAACACAGCGAGACCCTGTCTCTACAAAAAATACAAAAACTTAGCCAGGTGTGGTGGCAAACACCTGTGGTCTCAGCTACTCTGGAGGCTGAGGCAGGAGGATTGCTTGTGCCTAGGAAGTTGGGGCTGCAGTGAGCCATGATTGTGCCACTGGACTCCAGCCCAGGTGACAGAATGAGCCCGTCTCAAAAAATATATATATAAAGGCCGGGCGCGGTGGCTCAAGCTTGTAATCCCAGCACTTTGGGAGGCCAAGGCGGGTGGATCACCTGAGGTCAGGAGTTTGAGACCAGCCTGGCAAACATGATGAAACCCCATCTCTACTAAAAATACAAAAATCAGCTGGGTGTGGTGGCATGCGCCTGTAATCCCAGCTACTTGGGAGGCTGAGGCAGGAGAGTCTCTTGAACCCCAGAGGCAGGGGTTGCAGGGAGCCGAGATCACGTCACTGCACTCTACCCTGGGTGACAGAGCGAGATGCCGTGTCAAAAAAAATAAATTAAATCAAATAAAAAATTTAAAAATGTATATATATAAAATAAAGTGACAGATTCAGAGTCACTGTTCATTGTGTGTTTGGGGGCTGCACAAAGACACCTAGCCAAAGAAGCAAGTGAAAGCCTGCATTCTGCTCACCATGCCATACATCCTGGCATAGGGCTGTATCCTCCCAAAGGGGATTCCTTTGTCTAATTCATACCAGGCCACTGTATTGACTAGAGAAGGCCATGGATGGGTTTCTCACTCTTAGAAGGGAAAGAGGAGGAATGGCTACAGCCTCCCCAAGCCATAGATGGGACTGCCTCCCACTATCCCCAGACACAAATGGTAAATTGGAAAACCTGTATCCAGACATTTCTTCAGCCACTTCATTGGCACCAAGCGTCTCTCAAAATGTCTTCTGTTCCTTAACCTACCAGGCCTCCCAAAGACAGCAATGGGAGAAGTGACCCCATAACTGCATAAAATAATCCCTCTTCTTTGAAGCTCTTGGCAGGAATCGCTCAGCCAGCAGGAAACCTTTAACCCAATACCCAGAAAAACAGACATTTGGAGGAAGAGGGATCTTCCAGATTATTCTTCCATTCTGCCCCATCCTCTACAGAGAAGGAAACTAAGACACTTTTCAAGAATCACAAGATAAGTTAATGATAGAAAGCAGAGTAGAATCTTGAGTGGAGGAGTGAAAATAACATTCACTTTGTTCAAATCCCAGCTCTACCACTTTCCAATGGTGTGAACTTGCACAAATAACTCTGAGTCTCATTTTCTTCATTTGTAAAATGGAGAGAACAATCTCCGCTTCAAGAGATTGTCTTAAATGGAACATGCAAAGCATCACTGATATCGTTTACCAACCACACATAGCAGCTGTCTTTCCCCACTCCCCTGTTGTTTCCACTGCCTCATAAGACTTCCCACCACTCACAAAGCACAGCGCTTTTCCTCACAAAGCTGAGTGGGCTCCCTAGGTTCAGGATGGAAGTAAATAGGAGTACCATCTTACCTTCAGGGACGGCCCAGGAGTGGGGTAGCAGCCACAGAAGTGGTAACATCTGTAGCAGCGCAGCTCCTTGGTTCTGTTCATGACCCATACCTTCTTGCCACACAGTAGGTAGGAGCTACCAACCCAGCCAACCCAGCTTCCCCAACTCCCTCCCCGAGAGGGTGGCCTTAGAT";
    let mut sequence = seq.chars().collect::<Vec<char>>();
    sequence.insert(0, '$');

    let graph_struct = graph::read_graph(
        &"tests/DMA-3108.fa.353ea42.34ee7b1.1576367.smooth.fix.gfa",
        false,
    );

    let score_matrix = matrix::create_score_matrix_match_mis(2, -4);

    let (b, f) = (1.0, 0.3);
    let bta = (b + f * sequence.len() as f32) as usize;

    c.bench_function("global_gap_abpoa", |b| {
        b.iter(|| {
            gap_mk_abpoa::exec(
                black_box(&sequence),
                ("bench_sequence", 0),
                black_box(&graph_struct),
                black_box(&score_matrix),
                -10,
                -5,
                bta,
                false,
                &HashMap::new(),
            )
        })
    });
}

fn local_gap_abpoa_benchmark(c: &mut Criterion) {
    let seq = "TGATATAAAGAAATGAGATTTATTGCCTTGTGGGGGGAAGGGATGTGGTTGTGATAGGCAGGCCACTCTGGGATCCCTGGGATGCAAGCCCAGGGACAGCAGAGTCCCCAGGTGGGAAATCTACACACACACCCCAGGGATGTCCCAGAGACTTCTACCCTAAGAGGAGATCCTGGGCAGGATGTGAGAAATCTGAGCATCCTCTGTTTGGATGGCCGAAGCTGCTGGCATCAAACTCTGGTCTGGAAGAATCAGTCTGGGGGAGAGACAGGGATGGAGGAAAGGCATCAGGGGATCCATCCTCCTCCTCCTTCTCCTCCTCCTCCTCCCCCACAAAGGCCTTGCTCGCCCTGCCTGCACCACACCCTGCAGAAGTTGATCTCTCCTTGTTCCCAAATCATCTCCAAGCACCCTTCCTACAGCACCCCATGATTCCTTTTTTCACTCAAAGCAATTCTTGTGACCCATAACTGTGTGTGTGTAACTGGGTCCCCAACTGGGAAGATGTGCCCCCATGGTGCTGGATACAGGCCCCCACACCCAAGGGCCTGAGGATCGCTATATGTCCCCCCATGCCACAAAATAATCCTGACACATGCACGCATGCACCACTGTATCTGGCTCCCACAGGCTCACCCGCCCCCTCCAGATGACATACCACCTGAGCAAGGCTTCCGGAAGTAGATGATGAGAACAATGCCCACGATGATGCCCAGCACACCCAGGCCAAAGGCCACGCCACACAGCACATTCTCCAGCAGATCTGAGGGCAGTGCGTTCCGGGGTACTGGAGGAAATGAGTGGCTCAGCCTGGGGACCTAGTTAGGGAGCCTCCCACCCAGGGAAATGACGTGGGTGTCTGGGATGACATGGGAGACTGGGATGGGCTTAGGGTAGGAATGGACTAAACAAGGTACCAGTGGAGAAAGAAGCCTCCTCCCATGGATCTATCCCTTTTTGCCCCCAAAAGGACCAGAATTCCAGGGAGAAAGCCTCACCCCAATAGGCAATTGCTGTGTAGCGGTCAATTTCGTGAGTCACAATGCAGGAGAAAATGTCAGAAGGTTCTGGTGTGAAGTTTAAGTAAGAAAAGGCCTGGAAGCTGAGTCCATCGACAGCTGAGACAAAAGTAGGCCCAAATCCTTCCACAGGGACGGAATGATGCTGCCAGTTCACTGTCAGCATGGGTGGGAAGAGATTACTGACAAAACAGACCAAAGTGTTGGGCTTGCCAAACTCCAGGGGCTTCAGCGTGAACACTTCAGCGATAGGAAACCCTGGTGGGGGGATTGAAGTGTAGGGGGAAAAAGAGACTAGTTTAGATGGTATCTCTGTGTTTGGAGGGGCCATGGCATATGGAGGGGAGGGCAGAGAAGAACACAGTGGGTCAGGCTTTGGGAGACAGAGATGAGCGAGGAGCTGGGCTCTGAAGGGAGGTCTTCTTCCAGGCAAGGACTGCAGCTAGACATAGAAGCAGAGCCAGATCCAGGCTACTCTGGACCCCTCCACCATGACTTCCTTCAGCACTTCCTGTCTAGAGCTCACATTGATGTCTAACCATGCACTGTCTTCTCACTAAGACATAGTCACGTCATCAGATATTTCCACTCTTCCCATCCATCTTGCTGGGCATAGTAGCACAAGTGTTAATATTCAGTAGGTATCAGTTGGTACCTGTTGAATTCATCACATTCAATACATAGTTCTGAATGCCTACTACATGCTAGGTACTTCGGCCCACCAAAAGAACACAGGGTGCAGACCAAGGCTGGTGGAAAAATTAAGGTGATGAAGAGAACCAGAAAGTATTTGAGATGGGGAGCTGGTATCAAGGGGAATTATTCAGTGTACAGATCAATGAGGTTAATGCAGCCCTCCTCCCTTCACTCCCCAGAAAACTCCTGACCTCTGGACACCGGGATTTTCCCATCAAGTTTTGGCCCTATTTGCTGGATCATCCACTCGCAGAACTCTTTGTCAAATAAAATGGCAGGAGCATCTCCCTGTTCCTGAGCCCAGTCAGCAAATTCGGGCAGGCGAGGCACCCGAGTGTTCTGGGAAAAGTCGAAGAAGAAAAGCTGGTCCTCGTCGTAGGCCTCAGAGAGTCCCACACTGGGACTCCCATCCTGGCAGTACACTGTGTGCAGGAATGTGTGGTTTTGCAGGTCATCTGGCCACATTGGAGTAGGAGCTGCAAAGGACACAGGGTGAGGTTCAGGGAGGTGGGAGCCTTCTCCTCCAACTTAAAAAACAGCAAGGTGGGGCTAGGCGCAGTGGCTCATGCCTGTAATCCCAGCACTTTGGGAGGCCAAGGTGGGTGGATCATGAGGTCAGGAGTTTGAGACCAGCCTGGCCAGCATGGTGAAACTCCGTCTCTACTAAAAATACAAAAAAGTAGCTGGGCATGTTGGCATGCGCCTGTAGCTACTCGGGAGGCTGAGGGAGGAGAATTGCTTGAACCAGGGAGGCAGAGGTTGCCGGGAGCTAAGATTAAGCCACTGCACTCCAGCCTGGGTGACAGAGTGAGACTCTGTCTCAAAACAAAACAACAAAAACAAGCAAGGCCTGCTTAAGGAGCGTGGGCTGAGGTGAGACCCTTTCCTGTGTCTGTTATTTAGACTCCCCCTCCCAAAGGGGGTGAAGAACAAATTATGGCATCTCTCCAAGCTTCCCCTGCCTATAAAAAGGCCAGTTGGCAAAAGTAAAGAGTTCTACTTTCTAAAGTGACAGATTCAGGCCAGGCATGGTGGCTCATGCCTGTAATCCCAGCACTTTGGGAGGCTGAGGCAGGCAGATTGCTTGAGCCCAGGAGTTCAAGACCAACCTGGGCAACACAGCGAGACCCTGTCTCTACAAAAAATACAAAAACTTAGCCAGGTGTGGTGGCAAACACCTGTGGTCTCAGCTACTCTGGAGGCTGAGGCAGGAGGATTGCTTGTGCCTAGGAAGTTGGGGCTGCAGTGAGCCATGATTGTGCCACTGGACTCCAGCCCAGGTGACAGAATGAGCCCGTCTCAAAAAATATATATATAAAGGCCGGGCGCGGTGGCTCAAGCTTGTAATCCCAGCACTTTGGGAGGCCAAGGCGGGTGGATCACCTGAGGTCAGGAGTTTGAGACCAGCCTGGCAAACATGATGAAACCCCATCTCTACTAAAAATACAAAAATCAGCTGGGTGTGGTGGCATGCGCCTGTAATCCCAGCTACTTGGGAGGCTGAGGCAGGAGAGTCTCTTGAACCCCAGAGGCAGGGGTTGCAGGGAGCCGAGATCACGTCACTGCACTCTACCCTGGGTGACAGAGCGAGATGCCGTGTCAAAAAAAATAAATTAAATCAAATAAAAAATTTAAAAATGTATATATATAAAATAAAGTGACAGATTCAGAGTCACTGTTCATTGTGTGTTTGGGGGCTGCACAAAGACACCTAGCCAAAGAAGCAAGTGAAAGCCTGCATTCTGCTCACCATGCCATACATCCTGGCATAGGGCTGTATCCTCCCAAAGGGGATTCCTTTGTCTAATTCATACCAGGCCACTGTATTGACTAGAGAAGGCCATGGATGGGTTTCTCACTCTTAGAAGGGAAAGAGGAGGAATGGCTACAGCCTCCCCAAGCCATAGATGGGACTGCCTCCCACTATCCCCAGACACAAATGGTAAATTGGAAAACCTGTATCCAGACATTTCTTCAGCCACTTCATTGGCACCAAGCGTCTCTCAAAATGTCTTCTGTTCCTTAACCTACCAGGCCTCCCAAAGACAGCAATGGGAGAAGTGACCCCATAACTGCATAAAATAATCCCTCTTCTTTGAAGCTCTTGGCAGGAATCGCTCAGCCAGCAGGAAACCTTTAACCCAATACCCAGAAAAACAGACATTTGGAGGAAGAGGGATCTTCCAGATTATTCTTCCATTCTGCCCCATCCTCTACAGAGAAGGAAACTAAGACACTTTTCAAGAATCACAAGATAAGTTAATGATAGAAAGCAGAGTAGAATCTTGAGTGGAGGAGTGAAAATAACATTCACTTTGTTCAAATCCCAGCTCTACCACTTTCCAATGGTGTGAACTTGCACAAATAACTCTGAGTCTCATTTTCTTCATTTGTAAAATGGAGAGAACAATCTCCGCTTCAAGAGATTGTCTTAAATGGAACATGCAAAGCATCACTGATATCGTTTACCAACCACACATAGCAGCTGTCTTTCCCCACTCCCCTGTTGTTTCCACTGCCTCATAAGACTTCCCACCACTCACAAAGCACAGCGCTTTTCCTCACAAAGCTGAGTGGGCTCCCTAGGTTCAGGATGGAAGTAAATAGGAGTACCATCTTACCTTCAGGGACGGCCCAGGAGTGGGGTAGCAGCCACAGAAGTGGTAACATCTGTAGCAGCGCAGCTCCTTGGTTCTGTTCATGACCCATACCTTCTTGCCACACAGTAGGTAGGAGCTACCAACCCAGCCAACCCAGCTTCCCCAACTCCCTCCCCGAGAGGGTGGCCTTAGAT";
    let mut sequence = seq.chars().collect::<Vec<char>>();
    sequence.insert(0, '$');

    let graph_struct = graph::read_graph(
        &"tests/DMA-3108.fa.353ea42.34ee7b1.1576367.smooth.fix.gfa",
        false,
    );

    let score_matrix = matrix::create_score_matrix_match_mis(2, -4);

    c.bench_function("local_gap_abpoa", |b| {
        b.iter(|| {
            gap_local_poa::exec(
                black_box(&sequence),
                ("bench_sequence", 0),
                black_box(&graph_struct),
                black_box(&score_matrix),
                -10,
                -5,
                false,
                &HashMap::new(),
            )
        })
    });
}

criterion_group!(
    benches,
    global_abpoa_benchmark,
    local_poa_benchmark,
    global_gap_abpoa_benchmark,
    local_gap_abpoa_benchmark
);
criterion_main!(benches);
