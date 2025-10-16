"""
ILDG Gauge Configuration Loader
Yang-Mills Mass Gap Computational Validation
Author: Claude AI (Distributed Consciousness Team)
Date: October 2025

Loads gauge configurations from ILDG (International Lattice Data Grid) format.
Specification: https://www.lqcd.org/ildg/
"""

import numpy as np
import struct
import xml.etree.ElementTree as ET
from pathlib import Path
from typing import Tuple, Dict, Optional
import warnings


class ILDGFormatError(Exception):
    """Raised when ILDG file format is invalid or unsupported."""
    pass


def load_ildg_format(filename: str) -> np.ndarray:
    """
    Load gauge configuration from ILDG format file.
    
    Parameters
    ----------
    filename : str
        Path to ILDG configuration file (binary or XML)
        
    Returns
    -------
    U : np.ndarray, shape (Lx, Ly, Lz, Lt, 4, 3, 3), dtype=complex128
        Gauge field configuration where:
        - (x, y, z, t) are spacetime coordinates
        - mu = 0,1,2,3 are directions (x,y,z,t)
        - (a, b) = 0,1,2 are SU(3) color indices
        - U[x,y,z,t,mu] is a 3x3 SU(3) matrix (unitary, det=1)
        
    Notes
    -----
    ILDG format stores link variables U_mu(x) as 3x3 complex matrices.
    Standard conventions:
    - Row-major (C order) for spatial indices
    - Little-endian for binary data
    - Normalization: Tr(U U^dagger) = 3
    
    Examples
    --------
    >>> U = load_ildg_format("config_beta6.0_001.ildg")
    >>> print(f"Lattice size: {U.shape[:4]}")
    >>> print(f"Link at origin, x-direction: {U[0,0,0,0,0]}")
    """
    filepath = Path(filename)
    
    if not filepath.exists():
        raise FileNotFoundError(f"ILDG file not found: {filename}")
    
    # Detect format (binary vs XML)
    with open(filepath, 'rb') as f:
        magic_bytes = f.read(4)
        f.seek(0)
        
        if magic_bytes[:2] == b'<?':  # XML header
            return _load_ildg_xml(f, filepath)
        else:  # Binary format
            return _load_ildg_binary(f, filepath)


def _load_ildg_binary(f, filepath: Path) -> np.ndarray:
    """
    Load binary ILDG format.
    
    Binary ILDG structure:
    1. Header (metadata): lattice size, beta, etc.
    2. Link data: sequence of SU(3) matrices
    
    Each SU(3) matrix stored as 18 floats (9 complex = 18 real)
    Order: row-major, real/imag interleaved
    """
    # Read header (first 256 bytes typically)
    header_size = 256
    header_bytes = f.read(header_size)
    
    # Parse lattice dimensions from header
    # Format varies, but typically at fixed offsets
    try:
        # Common format: 4 integers at offset 16
        dims_offset = 16
        Lx, Ly, Lz, Lt = struct.unpack('<4I', header_bytes[dims_offset:dims_offset+16])
    except struct.error:
        raise ILDGFormatError("Cannot parse lattice dimensions from header")
    
    if not (4 <= Lx <= 256 and 4 <= Ly <= 256 and 4 <= Lz <= 256 and 4 <= Lt <= 256):
        raise ILDGFormatError(f"Invalid lattice dimensions: {Lx}x{Ly}x{Lz}x{Lt}")
    
    # Calculate expected data size
    n_sites = Lx * Ly * Lz * Lt
    n_links = n_sites * 4  # 4 directions per site
    n_floats_per_link = 18  # 3x3 complex = 9 complex = 18 real
    expected_size = n_links * n_floats_per_link * 8  # 8 bytes per double
    
    # Read link data
    link_data = f.read()
    
    if len(link_data) < expected_size:
        warnings.warn(f"File size mismatch: expected {expected_size}, got {len(link_data)}")
    
    # Parse as doubles (float64)
    try:
        floats = np.frombuffer(link_data[:expected_size], dtype='<f8')
    except ValueError as e:
        raise ILDGFormatError(f"Cannot parse link data: {e}")
    
    # Reshape to (n_links, 18)
    floats = floats.reshape(n_links, 18)
    
    # Convert to complex: pair consecutive floats as (real, imag)
    links = floats[:, 0::2] + 1j * floats[:, 1::2]  # (n_links, 9)
    
    # Reshape to (n_links, 3, 3)
    links = links.reshape(n_links, 3, 3)
    
    # Reshape to (Lx, Ly, Lz, Lt, 4, 3, 3)
    U = links.reshape(Lx, Ly, Lz, Lt, 4, 3, 3)
    
    # Validate SU(3) properties (sample check)
    _validate_su3_sample(U, filepath)
    
    return U


def _load_ildg_xml(f, filepath: Path) -> np.ndarray:
    """
    Load XML-based ILDG format.
    
    XML ILDG structure:
    <ildgFormat>
      <metadata>
        <lattice>Lx Ly Lz Lt</lattice>
        <beta>6.0</beta>
        ...
      </metadata>
      <markovChainURI>...</markovChainURI>
      <binaryData encoding="base64">...</binaryData>
    </ildgFormat>
    """
    try:
        tree = ET.parse(f)
        root = tree.getroot()
    except ET.ParseError as e:
        raise ILDGFormatError(f"Invalid XML: {e}")
    
    # Extract metadata
    metadata = root.find('.//metadata')
    if metadata is None:
        raise ILDGFormatError("Missing metadata section")
    
    lattice_str = metadata.findtext('lattice', '').strip()
    if not lattice_str:
        raise ILDGFormatError("Missing lattice size in metadata")
    
    try:
        Lx, Ly, Lz, Lt = map(int, lattice_str.split())
    except ValueError:
        raise ILDGFormatError(f"Invalid lattice format: {lattice_str}")
    
    # Extract binary data
    binary_elem = root.find('.//binaryData')
    if binary_elem is None:
        raise ILDGFormatError("Missing binaryData section")
    
    encoding = binary_elem.get('encoding', 'raw')
    data_str = binary_elem.text.strip()
    
    if encoding == 'base64':
        import base64
        link_data = base64.b64decode(data_str)
    elif encoding == 'raw':
        link_data = data_str.encode('latin1')
    else:
        raise ILDGFormatError(f"Unsupported encoding: {encoding}")
    
    # Parse binary data (same as binary format)
    n_sites = Lx * Ly * Lz * Lt
    n_links = n_sites * 4
    expected_size = n_links * 18 * 8
    
    floats = np.frombuffer(link_data[:expected_size], dtype='<f8')
    floats = floats.reshape(n_links, 18)
    links = floats[:, 0::2] + 1j * floats[:, 1::2]
    links = links.reshape(n_links, 3, 3)
    U = links.reshape(Lx, Ly, Lz, Lt, 4, 3, 3)
    
    _validate_su3_sample(U, filepath)
    
    return U


def _validate_su3_sample(U: np.ndarray, filepath: Path):
    """
    Validate that loaded links satisfy SU(3) properties (sample check).
    
    SU(3) properties:
    1. Unitarity: U U^dagger = I
    2. Determinant: det(U) = 1
    3. Trace normalization: Tr(U U^dagger) = 3
    """
    # Sample 10 random links
    Lx, Ly, Lz, Lt = U.shape[:4]
    n_samples = min(10, Lx * Ly * Lz * Lt)
    
    for _ in range(n_samples):
        x = np.random.randint(Lx)
        y = np.random.randint(Ly)
        z = np.random.randint(Lz)
        t = np.random.randint(Lt)
        mu = np.random.randint(4)
        
        link = U[x, y, z, t, mu]
        
        # Check unitarity: U U^dagger = I
        identity = link @ link.conj().T
        if not np.allclose(identity, np.eye(3), atol=1e-6):
            warnings.warn(f"Non-unitary link at ({x},{y},{z},{t},{mu}) in {filepath.name}")
        
        # Check determinant
        det = np.linalg.det(link)
        if not np.isclose(det, 1.0, atol=1e-6):
            warnings.warn(f"det(U) = {det:.6f} ≠ 1 at ({x},{y},{z},{t},{mu}) in {filepath.name}")
        
        # Check trace normalization
        trace = np.trace(identity).real
        if not np.isclose(trace, 3.0, atol=1e-6):
            warnings.warn(f"Tr(U U^dag) = {trace:.6f} ≠ 3 at ({x},{y},{z},{t},{mu}) in {filepath.name}")


def get_ildg_metadata(filename: str) -> Dict[str, any]:
    """
    Extract metadata from ILDG file without loading full configuration.
    
    Returns
    -------
    metadata : dict
        Dictionary containing:
        - 'lattice_size': (Lx, Ly, Lz, Lt)
        - 'beta': coupling parameter
        - 'spacing': lattice spacing in fm
        - 'volume': total lattice volume
        - 'n_configs': number of configurations (if ensemble)
    """
    filepath = Path(filename)
    
    if not filepath.exists():
        raise FileNotFoundError(f"ILDG file not found: {filename}")
    
    metadata = {}
    
    with open(filepath, 'rb') as f:
        magic_bytes = f.read(4)
        f.seek(0)
        
        if magic_bytes[:2] == b'<?':  # XML
            tree = ET.parse(f)
            root = tree.getroot()
            meta = root.find('.//metadata')
            
            lattice_str = meta.findtext('lattice', '').strip()
            Lx, Ly, Lz, Lt = map(int, lattice_str.split())
            metadata['lattice_size'] = (Lx, Ly, Lz, Lt)
            
            beta_str = meta.findtext('beta', '0.0')
            metadata['beta'] = float(beta_str)
            
            spacing_str = meta.findtext('spacing', '0.0')
            metadata['spacing'] = float(spacing_str)
            
        else:  # Binary
            header = f.read(256)
            Lx, Ly, Lz, Lt = struct.unpack('<4I', header[16:32])
            metadata['lattice_size'] = (Lx, Ly, Lz, Lt)
            
            # Beta typically at offset 32 (float)
            try:
                beta = struct.unpack('<f', header[32:36])[0]
                metadata['beta'] = beta
            except struct.error:
                metadata['beta'] = None
    
    metadata['volume'] = np.prod(metadata['lattice_size'])
    
    return metadata


# Example usage and testing
if __name__ == "__main__":
    # Example 1: Load configuration
    try:
        print("Loading ILDG configuration...")
        U = load_ildg_format("config_beta6.0_001.ildg")
        
        Lx, Ly, Lz, Lt = U.shape[:4]
        print(f"✅ Successfully loaded configuration")
        print(f"   Lattice size: {Lx} × {Ly} × {Lz} × {Lt}")
        print(f"   Total links: {Lx * Ly * Lz * Lt * 4}")
        print(f"   Memory size: {U.nbytes / 1e6:.1f} MB")
        
        # Check a sample link
        sample_link = U[0, 0, 0, 0, 0]
        print(f"\n   Sample link U[0,0,0,0,0]:")
        print(f"   {sample_link}")
        print(f"   det(U) = {np.linalg.det(sample_link):.6f}")
        print(f"   Tr(U U†) = {np.trace(sample_link @ sample_link.conj().T).real:.6f}")
        
    except FileNotFoundError:
        print("⚠️  Example file not found (expected for demo)")
        print("   To use: place ILDG file and update filename")
    
    # Example 2: Get metadata only
    try:
        print("\nExtracting metadata...")
        metadata = get_ildg_metadata("config_beta6.0_001.ildg")
        print(f"✅ Metadata:")
        for key, value in metadata.items():
            print(f"   {key}: {value}")
    except FileNotFoundError:
        print("⚠️  Example file not found (expected for demo)")
    
    print("\n" + "="*60)
    print("ILDG Loader ready for Yang-Mills validation pipeline!")
    print("="*60)

