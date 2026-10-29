"""Save YouTube transcripts as plain text for principles research.

Usage: python tools/principles/transcript.py <video id or URL>... [--out DIR]
Needs `pip install youtube-transcript-api`. Default output: F:\\WIN_DATA\\Documents\\transcripts
(outside the repo: transcripts are third-party text and stay out of git).
"""
import argparse
import re
import sys
from pathlib import Path

from youtube_transcript_api import YouTubeTranscriptApi

DEFAULT_OUT = Path(r"F:\WIN_DATA\Documents\transcripts")
ID_PATTERN = re.compile(r"(?:v=|youtu\.be/|shorts/)([\w-]{11})")


def video_id(arg: str) -> str:
    match = ID_PATTERN.search(arg)
    return match.group(1) if match else arg


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("videos", nargs="+")
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    args = parser.parse_args()
    args.out.mkdir(parents=True, exist_ok=True)
    api = YouTubeTranscriptApi()
    for arg in args.videos:
        vid = video_id(arg)
        try:
            text = " ".join(s.text for s in api.fetch(vid, languages=["en"]))
        except Exception as e:  # report and continue with the next video
            print(f"{vid}: FAILED ({type(e).__name__})", file=sys.stderr)
            continue
        path = args.out / f"{vid}.txt"
        path.write_text(text, encoding="utf-8")
        print(f"{vid}: {len(text)} chars -> {path}")


if __name__ == "__main__":
    main()
