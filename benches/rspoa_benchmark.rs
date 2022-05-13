#![feature(stdsimd)]

use std::collections::HashMap;

use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion};
use rspoa::{
    gap_local_poa, gap_mk_abpoa, global_mk_abpoa, graph, local_poa, matrix, simd_abpoa_m_mm,
    simd_poa,
};
/*
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
    let hofp = HashMap::new();
    c.bench_function("global_abpoa", |b| {
        b.iter(|| {
            global_mk_abpoa::exec(
                black_box(&sequence),
                ("bench_sequence", 0),
                black_box(&graph_struct),
                black_box(&score_matrix),
                bta,
                false,
                &hofp,
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
    let hofp = HashMap::new();

    c.bench_function("local_abpoa", |b| {
        b.iter(|| {
            local_poa::exec(
                black_box(&sequence),
                ("bench_sequence", 0),
                black_box(&graph_struct),
                black_box(&score_matrix),
                false,
                &hofp,
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
    let hofp = HashMap::new();

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
                &hofp,
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
    let hofp = HashMap::new();

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
                &hofp,
            )
        })
    });
}
*/
fn bench_poa_eds(c: &mut Criterion) {
    let mut group = c.benchmark_group("Partial Order Alignment");
    let graph_struct = graph::read_graph(
        &"tests/DMA-3108.fa.353ea42.34ee7b1.1576367.smooth.fix.gfa",
        false,
    );
    let seq = "TGATATAAAGAAATGAGATTTATTGCCTTGTGGGGGGAAGGGATGTGGTTGTGATAGGCAGGCCACTCTGGGATCCCTGGGATGCAAGCCCAGGGACAGCAGAGTCCCCAGGTGGGAAATCTACACACACACCCCAGGGATGTCCCAGAGACTTCTACCCTAAGAGGAGATCCTGGGCAGGATGTGAGAAATCTGAGCATCCTCTGTTTGGATGGCCGAAGCTGCTGGCATCAAACTCTGGTCTGGAAGAATCAGTCTGGGGGAGAGACAGGGATGGAGGAAAGGCATCAGGGGATCCATCCTCCTCCTCCTTCTCCTCCTCCTCCTCCCCCACAAAGGCCTTGCTCGCCCTGCCTGCACCACACCCTGCAGAAGTTGATCTCTCCTTGTTCCCAAATCATCTCCAAGCACCCTTCCTACAGCACCCCATGATTCCTTTTTTCACTCAAAGCAATTCTTGTGACCCATAACTGTGTGTGTGTAACTGGGTCCCCAACTGGGAAGATGTGCCCCCATGGTGCTGGATACAGGCCCCCACACCCAAGGGCCTGAGGATCGCTATATGTCCCCCCATGCCACAAAATAATCCTGACACATGCACGCATGCACCACTGTATCTGGCTCCCACAGGCTCACCCGCCCCCTCCAGATGACATACCACCTGAGCAAGGCTTCCGGAAGTAGATGATGAGAACAATGCCCACGATGATGCCCAGCACACCCAGGCCAAAGGCCACGCCACACAGCACATTCTCCAGCAGATCTGAGGGCAGTGCGTTCCGGGGTACTGGAGGAAATGAGTGGCTCAGCCTGGGGACCTAGTTAGGGAGCCTCCCACCCAGGGAAATGACGTGGGTGTCTGGGATGACATGGGAGACTGGGATGGGCTTAGGGTAGGAATGGACTAAACAAGGTACCAGTGGAGAAAGAAGCCTCCTCCCATGGATCTATCCCTTTTTGCCCCCAAAAGGACCAGAATTCCAGGGAGAAAGCCTCACCCCAATAGGCAATTGCTGTGTAGCGGTCAATTTCGTGAGTCACAATGCAGGAGAAAATGTCAGAAGGTTCTGGTGTGAAGTTTAAGTAAGAAAAGGCCTGGAAGCTGAGTCCATCGACAGCTGAGACAAAAGTAGGCCCAAATCCTTCCACAGGGACGGAATGATGCTGCCAGTTCACTGTCAGCATGGGTGGGAAGAGATTACTGACAAAACAGACCAAAGTGTTGGGCTTGCCAAACTCCAGGGGCTTCAGCGTGAACACTTCAGCGATAGGAAACCCTGGTGGGGGGATTGAAGTGTAGGGGGAAAAAGAGACTAGTTTAGATGGTATCTCTGTGTTTGGAGGGGCCATGGCATATGGAGGGGAGGGCAGAGAAGAACACAGTGGGTCAGGCTTTGGGAGACAGAGATGAGCGAGGAGCTGGGCTCTGAAGGGAGGTCTTCTTCCAGGCAAGGACTGCAGCTAGACATAGAAGCAGAGCCAGATCCAGGCTACTCTGGACCCCTCCACCATGACTTCCTTCAGCACTTCCTGTCTAGAGCTCACATTGATGTCTAACCATGCACTGTCTTCTCACTAAGACATAGTCACGTCATCAGATATTTCCACTCTTCCCATCCATCTTGCTGGGCATAGTAGCACAAGTGTTAATATTCAGTAGGTATCAGTTGGTACCTGTTGAATTCATCACATTCAATACATAGTTCTGAATGCCTACTACATGCTAGGTACTTCGGCCCACCAAAAGAACACAGGGTGCAGACCAAGGCTGGTGGAAAAATTAAGGTGATGAAGAGAACCAGAAAGTATTTGAGATGGGGAGCTGGTATCAAGGGGAATTATTCAGTGTACAGATCAATGAGGTTAATGCAGCCCTCCTCCCTTCACTCCCCAGAAAACTCCTGACCTCTGGACACCGGGATTTTCCCATCAAGTTTTGGCCCTATTTGCTGGATCATCCACTCGCAGAACTCTTTGTCAAATAAAATGGCAGGAGCATCTCCCTGTTCCTGAGCCCAGTCAGCAAATTCGGGCAGGCGAGGCACCCGAGTGTTCTGGGAAAAGTCGAAGAAGAAAAGCTGGTCCTCGTCGTAGGCCTCAGAGAGTCCCACACTGGGACTCCCATCCTGGCAGTACACTGTGTGCAGGAATGTGTGGTTTTGCAGGTCATCTGGCCACATTGGAGTAGGAGCTGCAAAGGACACAGGGTGAGGTTCAGGGAGGTGGGAGCCTTCTCCTCCAACTTAAAAAACAGCAAGGTGGGGCTAGGCGCAGTGGCTCATGCCTGTAATCCCAGCACTTTGGGAGGCCAAGGTGGGTGGATCATGAGGTCAGGAGTTTGAGACCAGCCTGGCCAGCATGGTGAAACTCCGTCTCTACTAAAAATACAAAAAAGTAGCTGGGCATGTTGGCATGCGCCTGTAGCTACTCGGGAGGCTGAGGGAGGAGAATTGCTTGAACCAGGGAGGCAGAGGTTGCCGGGAGCTAAGATTAAGCCACTGCACTCCAGCCTGGGTGACAGAGTGAGACTCTGTCTCAAAACAAAACAACAAAAACAAGCAAGGCCTGCTTAAGGAGCGTGGGCTGAGGTGAGACCCTTTCCTGTGTCTGTTATTTAGACTCCCCCTCCCAAAGGGGGTGAAGAACAAATTATGGCATCTCTCCAAGCTTCCCCTGCCTATAAAAAGGCCAGTTGGCAAAAGTAAAGAGTTCTACTTTCTAAAGTGACAGATTCAGGCCAGGCATGGTGGCTCATGCCTGTAATCCCAGCACTTTGGGAGGCTGAGGCAGGCAGATTGCTTGAGCCCAGGAGTTCAAGACCAACCTGGGCAACACAGCGAGACCCTGTCTCTACAAAAAATACAAAAACTTAGCCAGGTGTGGTGGCAAACACCTGTGGTCTCAGCTACTCTGGAGGCTGAGGCAGGAGGATTGCTTGTGCCTAGGAAGTTGGGGCTGCAGTGAGCCATGATTGTGCCACTGGACTCCAGCCCAGGTGACAGAATGAGCCCGTCTCAAAAAATATATATATAAAGGCCGGGCGCGGTGGCTCAAGCTTGTAATCCCAGCACTTTGGGAGGCCAAGGCGGGTGGATCACCTGAGGTCAGGAGTTTGAGACCAGCCTGGCAAACATGATGAAACCCCATCTCTACTAAAAATACAAAAATCAGCTGGGTGTGGTGGCATGCGCCTGTAATCCCAGCTACTTGGGAGGCTGAGGCAGGAGAGTCTCTTGAACCCCAGAGGCAGGGGTTGCAGGGAGCCGAGATCACGTCACTGCACTCTACCCTGGGTGACAGAGCGAGATGCCGTGTCAAAAAAAATAAATTAAATCAAATAAAAAATTTAAAAATGTATATATATAAAATAAAGTGACAGATTCAGAGTCACTGTTCATTGTGTGTTTGGGGGCTGCACAAAGACACCTAGCCAAAGAAGCAAGTGAAAGCCTGCATTCTGCTCACCATGCCATACATCCTGGCATAGGGCTGTATCCTCCCAAAGGGGATTCCTTTGTCTAATTCATACCAGGCCACTGTATTGACTAGAGAAGGCCATGGATGGGTTTCTCACTCTTAGAAGGGAAAGAGGAGGAATGGCTACAGCCTCCCCAAGCCATAGATGGGACTGCCTCCCACTATCCCCAGACACAAATGGTAAATTGGAAAACCTGTATCCAGACATTTCTTCAGCCACTTCATTGGCACCAAGCGTCTCTCAAAATGTCTTCTGTTCCTTAACCTACCAGGCCTCCCAAAGACAGCAATGGGAGAAGTGACCCCATAACTGCATAAAATAATCCCTCTTCTTTGAAGCTCTTGGCAGGAATCGCTCAGCCAGCAGGAAACCTTTAACCCAATACCCAGAAAAACAGACATTTGGAGGAAGAGGGATCTTCCAGATTATTCTTCCATTCTGCCCCATCCTCTACAGAGAAGGAAACTAAGACACTTTTCAAGAATCACAAGATAAGTTAATGATAGAAAGCAGAGTAGAATCTTGAGTGGAGGAGTGAAAATAACATTCACTTTGTTCAAATCCCAGCTCTACCACTTTCCAATGGTGTGAACTTGCACAAATAACTCTGAGTCTCATTTTCTTCATTTGTAAAATGGAGAGAACAATCTCCGCTTCAAGAGATTGTCTTAAATGGAACATGCAAAGCATCACTGATATCGTTTACCAACCACACATAGCAGCTGTCTTTCCCCACTCCCCTGTTGTTTCCACTGCCTCATAAGACTTCCCACCACTCACAAAGCACAGCGCTTTTCCTCACAAAGCTGAGTGGGCTCCCTAGGTTCAGGATGGAAGTAAATAGGAGTACCATCTTACCTTCAGGGACGGCCCAGGAGTGGGGTAGCAGCCACAGAAGTGGTAACATCTGTAGCAGCGCAGCTCCTTGGTTCTGTTCATGACCCATACCTTCTTGCCACACAGTAGGTAGGAGCTACCAACCCAGCCAACCCAGCTTCCCCAACTCCCTCCCCGAGAGGGTGGCCTTAGAT".chars().map(|c| c as u8).collect::<Vec<u8>>();
    let m = 2f32;
    let mm = -4f32;
    for i in [1, 2, 3].iter() {
        unsafe {
            group.bench_with_input(BenchmarkId::new(" No Simd", i), i, |b, _i| {
                b.iter(|| {
                    simd_poa::exec_no_simd(
                        black_box(&seq),
                        black_box(&graph_struct),
                        black_box(m),
                        black_box(mm),
                    )
                })
            });

            group.bench_with_input(BenchmarkId::new(" Simd (avx2)", i), i, |b, _i| {
                b.iter(|| {
                    simd_poa::exec(
                        black_box(&seq),
                        black_box(&graph_struct),
                        black_box(m),
                        black_box(mm),
                    )
                })
            });

            group.bench_with_input(BenchmarkId::new(" Simd and ab", i), i, |b, _i| {
                b.iter(|| {
                    simd_abpoa_m_mm::exec(
                        black_box(&seq),
                        black_box(&graph_struct),
                        black_box(m),
                        black_box(mm),
                        5,
                    )
                })
            });
        }
    }
    group.finish();
}

criterion_group!(
    benches,
    bench_poa_eds,
    /*
    global_abpoa_benchmark,
    local_poa_benchmark,
    global_gap_abpoa_benchmark,
    local_gap_abpoa_benchmark,
    */
);
criterion_main!(benches);
