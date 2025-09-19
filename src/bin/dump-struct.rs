use std::mem;

use ubiblk::block_device::StripeFetcher;

fn main()
{
   println!("StripeFetcher size: {}", mem::size_of::<StripeFetcher>());
   println!("fetch_queue offset: {}", mem::offset_of!(StripeFetcher, fetch_queue));
   println!("stripes_fetched offset: {}", mem::offset_of!(StripeFetcher, stripes_fetched));
   println!("pending_flush_requests offset: {}", mem::offset_of!(StripeFetcher, pending_flush_requests));
   println!("inprogress_flush_requests offset: {}", mem::offset_of!(StripeFetcher, inprogress_flush_requests));
   println!("source_sector_count offset: {}", mem::offset_of!(StripeFetcher, source_sector_count));
   println!("target_sector_count offset: {}", mem::offset_of!(StripeFetcher, target_sector_count));
}