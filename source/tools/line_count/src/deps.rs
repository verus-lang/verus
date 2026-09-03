// parse the .d file and returns a vector of files names required to generate the crate
pub fn get_dependencies(
    dep_file_path: &std::path::Path,
) -> Result<(std::path::PathBuf, Vec<std::path::PathBuf>), String> {
    use std::path::{Path, PathBuf};

    let file = std::fs::File::open(dep_file_path)
        .map_err(|x| format!("{}, dependency file name: {:?}", x, dep_file_path))?;
    let mut reader = std::io::BufReader::new(file);
    let mut dependencies = String::new();
    std::io::BufRead::read_line(&mut reader, &mut dependencies).map_err(|x| {
        format!("Could not read the first line of the dependency file with message: {}", x)
    })?;
    let dep_file_folder = dep_file_path
        .parent()
        .ok_or(format!("invalid dependencies file path {}", dep_file_path.display()))?;
    let result: Vec<_> = dependencies
        .split_whitespace()
        .skip(1)
        .map(|x| dep_file_folder.join(Path::new(x)))
        .collect();
    assert!(result.len() > 0);

    if result.len() == 1 {
        return Ok((PathBuf::new(), vec![result[0].clone()]));
    }

    let mut path_iters: Vec<_> = result.iter().map(|x| x.iter()).collect();
    let mut chomp_components = 0;
    loop {
        let common = path_iters
            .iter_mut()
            .map(|x| x.next())
            .reduce(|acc, x| acc.filter(|&a| Some(a) == x))
            .flatten();
        if common.is_some() {
            chomp_components += 1;
        } else {
            break;
        }
    }
    let result_chomped: Vec<PathBuf> =
        result.iter().map(|p| PathBuf::from_iter(p.components().skip(chomp_components))).collect();
    let chomped = PathBuf::from_iter(result[0].iter().take(chomp_components));

    Ok((chomped, result_chomped))
}
