
import os
import re
from anthropic import Anthropic

client = Anthropic(api_key=os.environ.get("ANTHROPIC_API_KEY"))

# Read AxiomProofs.lean
with open('../formal/AxiomProofs.lean', 'r') as f:
    content = f.read()

# Find first sorry
match = re.search(r'by sorry', content)
if match:
    print(f"Found sorry at position {match.start()}")
    
    # Extract context (500 chars before)
    start = max(0, match.start() - 500)
    context = content[start:match.start()]
    
    # Get theorem name
    theorem_match = re.search(r'theorem\s+(\w+)', context)
    theorem_name = theorem_match.group(1) if theorem_match else "unknown"
    
    print(f"Theorem: {theorem_name}")
    print("Context:", context[-200:])
    
    # Generate proof with Claude
    prompt = f"""Complete this Lean 4 proof. Context:
{context}
by sorry

Provide ONLY the proof code starting with 'by', nothing else."""
    
    response = client.messages.create(
        model="claude-opus-4-20250514",
        max_tokens=500,
        temperature=0,
        messages=[{"role": "user", "content": prompt}]
    )
    
    proof = response.content[0].text.strip()
    print(f"Generated proof: {proof}")
else:
    print("No sorries found")
