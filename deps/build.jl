using BinaryProvider
using Libdl

# Parse some basic command-line arguments
const verbose = "--verbose" in ARGS
const prefix = Prefix(get([a for a in ARGS if a != "--verbose"], 1, joinpath(@__DIR__, "usr")))
products = [
    LibraryProduct(prefix, String["cryptominisat5.5.5"], :libcms),
]

# Download binaries from hosted location
bin_prefix = "https://github.com/..."

# Listing of files generated by BinaryBuilder:
download_info = Dict(
    #BinaryProvider.Linux(:aarch64, :glibc, :blank_abi) => ("$bin_prefix/Zlib.aarch64-linux-gnu.tar.gz", "f5ad5b4390ddd6d6a96cc573b5b6aadce31977698355658f03a62351f02f8e2d"),
    #BinaryProvider.UnknownPlatform() => ("$bin_prefix/Zlib.arm-linux-gnueabihf.tar.gz", "ea00d81a87aa1159348ae570f17398eb5fb6ffea1c8e97751cb4aa5db2e00acf"),
    #BinaryProvider.Linux(:i686, :glibc, :blank_abi) => ("$bin_prefix/Zlib.i686-linux-gnu.tar.gz", "20afcaf2536f43b35814d56bd8a26cd39b068ffe1a513c21dc61d600ef8b4bee"),
    #BinaryProvider.Windows(:i686, :blank_libc, :blank_abi) => ("$bin_prefix/Zlib.i686-w64-mingw32.tar.gz", "1b85dc6e98e7677b63e6cf7ce97718e892cfdd858b7a210b723ce1b5c86e48d7"),
    #BinaryProvider.MacOS(:x86_64, :blank_libc, :blank_abi) => ("$bin_prefix/Zlib.x86_64-apple-darwin14.tar.gz", "924f13195b3b95c4d23f3828ecb6ae3b1c8f3a1c4d5372a13090cff4e7ed1c4a"),
    #BinaryProvider.Linux(:x86_64, :glibc, :blank_abi) => ("$bin_prefix/Zlib.x86_64-linux-gnu.tar.gz", "769aee697443ef7111bab843df304f50eedd671006fad9f49913abed0dbac64b"),
    #BinaryProvider.Windows(:x86_64, :blank_libc, :blank_abi) => ("$bin_prefix/Zlib.x86_64-w64-mingw32.tar.gz", "4479f1b7559227767e305520efe077f575b3edc7cb59235dbdca33e09a756ed1"),
#    BinaryProvider.Linux(:aarch64, :glibc) => ("$bin_prefix/Zlib.aarch64-linux-gnu.tar.gz", "f5ad5b4390ddd6d6a96cc573b5b6aadce31977698355658f03a62351f02f8e2d"),
#    BinaryProvider.Linux(:i686, :glibc) => ("$bin_prefix/Zlib.i686-linux-gnu.tar.gz", "20afcaf2536f43b35814d56bd8a26cd39b068ffe1a513c21dc61d600ef8b4bee"),
#    BinaryProvider.Windows(:i686) => ("$bin_prefix/Zlib.i686-w64-mingw32.tar.gz", "1b85dc6e98e7677b63e6cf7ce97718e892cfdd858b7a210b723ce1b5c86e48d7"),
#    BinaryProvider.MacOS(:x86_64) => ("$bin_prefix/Zlib.x86_64-apple-darwin14.tar.gz", "924f13195b3b95c4d23f3828ecb6ae3b1c8f3a1c4d5372a13090cff4e7ed1c4a"),
#    BinaryProvider.Linux(:x86_64, :glibc) => ("$bin_prefix/Zlib.x86_64-linux-gnu.tar.gz", "769aee697443ef7111bab843df304f50eedd671006fad9f49913abed0dbac64b"),
#    BinaryProvider.Windows(:x86_64) => ("$bin_prefix/Zlib.x86_64-w64-mingw32.tar.gz", "4479f1b7559227767e305520efe077f575b3edc7cb59235dbdca33e09a756ed1"),
)

# A simple source build fallback for platforms not supported by BinaryBuilder
# Assumes that tar, GNU make, and a C compiler are available
function sourcebuild()
    srcdir = joinpath(@__DIR__, "src")
    libdir = joinpath(@__DIR__, "lib")
    ver = "5.6.8"
    dir = "cryptominisat-$ver"
    for d = [srcdir, libdir]
        isdir(d) && rm(d, force=true, recursive=true)
        mkpath(d)
    end
    download("https://github.com/msoos/cryptominisat/archive/$ver.tar.gz", joinpath(srcdir, "$dir.tar.gz"))
    cd(srcdir) do
        run(`tar xzf $dir.tar.gz`)
    end
    cd(joinpath(srcdir, dir)) do
        run(`cmake .`)
        run(`make -j$(Sys.CPU_THREADS)`)
    end
    libcms = "libcryptominisat5." * Libdl.dlext
    found = false
    for f in readdir(joinpath(srcdir, dir, "lib"))
        if startswith(f, libcms)
            found = true
            cp(joinpath(srcdir, dir, "lib", f), joinpath(libdir, f), force=true, follow_symlinks=true)
        end
    end
    found || error("cryptominisat was unable to build properly")
    libcms = joinpath(libdir, libcms)
    open(joinpath(@__DIR__, "deps.jl"), "w") do io
        println(io, """
            using Libdl
            function check_deps()
                ptr = Libdl.dlopen_e("$libcms")
                loaded = ptr != C_NULL
                Libdl.dlclose(ptr)
                if !loaded
                    error("Unable to load $libcms. Please rerun " *
                          "`Pkg.build(\\"CryptoMiniSat\\")` and restart Julia.")
                end
            end
            const libcms = "$libcms"
            """)
    end
end

if any(!satisfied(p; verbose=verbose) for p in products)
    # Check to see if we're all satisfied
    if haskey(download_info, platform_key_abi())
        # Download and install binaries
        url, tarball_hash = download_info[platform_key_abi()]
        install(url, tarball_hash; prefix=prefix, force=true, verbose=verbose)
        write_deps_file(joinpath(@__DIR__, "deps.jl"), products)
    else
        sourcebuild()
    end
end