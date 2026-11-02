use std::sync::atomic::AtomicBool;

use crate::miner::Mined;
use crate::mining::Pow;

#[cfg(not(target_os = "macos"))]
mod cuda;
#[cfg(target_os = "macos")]
mod metal;

#[derive(Clone, Debug)]
pub struct Device {
    pub index: usize,
    pub name: String,
    pub mem_bytes: u64,
}

pub fn devices() -> Vec<Device> {
    #[cfg(not(target_os = "macos"))]
    {
        cuda::devices()
    }
    #[cfg(target_os = "macos")]
    {
        metal::devices()
    }
}

pub fn mine(dev: &Device, pow: Pow, seconds: f64, stop: &AtomicBool, progress: &mut dyn FnMut(Mined)) -> Result<Mined, String> {
    #[cfg(not(target_os = "macos"))]
    {
        cuda::mine(dev, pow, seconds, stop, progress)
    }
    #[cfg(target_os = "macos")]
    {
        metal::mine(dev, pow, seconds, stop, progress)
    }
}

pub(crate) fn reference(pow: Pow, header: &[u8], nonce: u64) -> Vec<u8> {
    crate::mining::fast_hash(pow, header, nonce).to_vec()
}
