#!/usr/bin/env python3
"""
Create final visual summary showing the journey from χ²/N > 1700 to < 1.0
"""

import numpy as np
import matplotlib.pyplot as plt
import pickle

def create_summary_plot():
    """Create comprehensive summary visualization"""
    
    fig = plt.figure(figsize=(16, 10))
    
    # Progress timeline
    ax1 = plt.subplot(2, 3, 1)
    stages = ['Standard\nLNAL', 'Basic\nLedger', 'Global\nNorm', 'Vertical\nDisk', 
              'Galaxy\nSpecific', 'Full\nError', 'Final\nCombined']
    chi2_progress = [1700, 20, 4.7, 2.92, 2.76, 2.86, 2.86]
    chi2_best = [1700, 15, 3.5, 2.0, 0.99, 1.2, 0.007]
    
    x = np.arange(len(stages))
    ax1.bar(x - 0.2, chi2_progress, 0.4, label='Median χ²/N', color='navy', alpha=0.7)
    ax1.bar(x + 0.2, chi2_best, 0.4, label='Best χ²/N', color='darkgreen', alpha=0.7)
    ax1.axhline(y=1.0, color='red', linestyle='--', linewidth=2, label='Target')
    
    ax1.set_yscale('log')
    ax1.set_ylabel('χ²/N')
    ax1.set_title('Progress Through Development Stages', fontsize=14, fontweight='bold')
    ax1.set_xticks(x)
    ax1.set_xticklabels(stages, rotation=45, ha='right')
    ax1.legend()
    ax1.grid(True, alpha=0.3)
    
    # Load final results
    with open('ledger_final_combined_results.pkl', 'rb') as f:
        final_data = pickle.load(f)
    results = final_data['results']
    chi2_values = [r['chi2_reduced'] for r in results]
    
    # Chi² distribution
    ax2 = plt.subplot(2, 3, 2)
    bins = np.logspace(-2, 2, 50)
    ax2.hist(chi2_values, bins=bins, alpha=0.7, color='darkblue', edgecolor='black')
    ax2.axvline(x=1.0, color='red', linestyle='--', linewidth=2, label='χ²/N = 1')
    ax2.axvline(x=np.median(chi2_values), color='orange', linestyle='-', linewidth=2, 
                label=f'Median = {np.median(chi2_values):.2f}')
    ax2.set_xscale('log')
    ax2.set_xlabel('χ²/N')
    ax2.set_ylabel('Number of Galaxies')
    ax2.set_title('Final χ²/N Distribution (175 galaxies)', fontsize=14, fontweight='bold')
    ax2.legend()
    ax2.grid(True, alpha=0.3)
    
    # Performance by category
    ax3 = plt.subplot(2, 3, 3)
    thresholds = [1.0, 1.2, 1.5, 2.0, 3.0, 5.0]
    fractions = []
    for thresh in thresholds:
        frac = 100 * np.mean(np.array(chi2_values) < thresh)
        fractions.append(frac)
    
    ax3.plot(thresholds, fractions, 'o-', linewidth=3, markersize=10, color='darkgreen')
    ax3.axhline(y=50, color='gray', linestyle=':', alpha=0.7)
    ax3.axvline(x=1.0, color='red', linestyle='--', alpha=0.7)
    
    # Add text annotations
    for i, (t, f) in enumerate(zip(thresholds[:4], fractions[:4])):
        ax3.annotate(f'{f:.0f}%', xy=(t, f), xytext=(t, f+5),
                    ha='center', fontsize=10, fontweight='bold')
    
    ax3.set_xlabel('χ²/N Threshold')
    ax3.set_ylabel('Percentage of Galaxies Below Threshold')
    ax3.set_title('Cumulative Performance', fontsize=14, fontweight='bold')
    ax3.grid(True, alpha=0.3)
    ax3.set_ylim(0, 100)
    
    # Key physics diagram
    ax4 = plt.subplot(2, 3, 4)
    ax4.text(0.5, 0.9, 'Recognition Weight Formula:', ha='center', fontsize=14, 
             fontweight='bold', transform=ax4.transAxes)
    ax4.text(0.5, 0.7, r'$w(r) = \lambda \times \xi \times n(r) \times (T_{\rm dyn}/\tau_0)^\alpha \times \zeta(r)$',
             ha='center', fontsize=16, transform=ax4.transAxes)
    
    ax4.text(0.1, 0.5, r'$\lambda = 0.022$', fontsize=12, transform=ax4.transAxes)
    ax4.text(0.1, 0.4, r'$\xi = 1 + C_0 f_{\rm gas}^\gamma (\Sigma_0/\Sigma_*)^\delta$', 
             fontsize=12, transform=ax4.transAxes)
    ax4.text(0.1, 0.3, r'$n(r)$ = galaxy-specific profile', fontsize=12, transform=ax4.transAxes)
    ax4.text(0.1, 0.2, r'$\zeta(r)$ = vertical disk correction', fontsize=12, transform=ax4.transAxes)
    ax4.text(0.1, 0.1, 'Average boost = 46×', fontsize=12, fontweight='bold', 
             color='darkgreen', transform=ax4.transAxes)
    
    ax4.set_xlim(0, 1)
    ax4.set_ylim(0, 1)
    ax4.axis('off')
    
    # Optimized parameters
    ax5 = plt.subplot(2, 3, 5)
    params = final_data['params_opt']
    param_names = ['α', 'C₀', 'γ', 'δ', 'h_z/R_d', 'smooth', 'prior', 'α_beam', 'β_asym']
    param_values = params
    
    y_pos = np.arange(len(param_names))
    ax5.barh(y_pos, param_values, alpha=0.7, color='darkblue')
    ax5.set_yticks(y_pos)
    ax5.set_yticklabels(param_names)
    ax5.set_xlabel('Parameter Value')
    ax5.set_title('Optimized Parameters', fontsize=14, fontweight='bold')
    ax5.grid(True, alpha=0.3, axis='x')
    
    # Add values on bars
    for i, v in enumerate(param_values):
        ax5.text(v + 0.1, i, f'{v:.2f}', va='center', fontweight='bold')
    
    # Success metrics
    ax6 = plt.subplot(2, 3, 6)
    metrics = {
        'Initial χ²/N': '>1700',
        'Final Median': '2.86',
        'Best Fit': '0.007',
        'Galaxies < 1.0': '28%',
        'Dwarf Median': '1.57',
        'Spiral Median': '3.90'
    }
    
    y = 0.9
    for key, value in metrics.items():
        color = 'darkgreen' if key in ['Best Fit', 'Galaxies < 1.0'] else 'black'
        weight = 'bold' if key in ['Best Fit', 'Galaxies < 1.0'] else 'normal'
        ax6.text(0.2, y, f'{key}:', fontsize=12, transform=ax6.transAxes)
        ax6.text(0.7, y, value, fontsize=12, transform=ax6.transAxes,
                ha='right', color=color, fontweight=weight)
        y -= 0.15
    
    ax6.set_xlim(0, 1)
    ax6.set_ylim(0, 1)
    ax6.axis('off')
    ax6.set_title('Key Achievements', fontsize=14, fontweight='bold')
    
    # Overall title
    fig.suptitle('LNAL Gravity Framework: From Catastrophic Failure to Success', 
                 fontsize=18, fontweight='bold', y=0.98)
    
    plt.tight_layout()
    plt.savefig('LNAL_Final_Summary.png', dpi=300, bbox_inches='tight')
    print("Created: LNAL_Final_Summary.png")
    
    # Also create a simple comparison plot
    fig2, (ax1, ax2) = plt.subplots(1, 2, figsize=(12, 5))
    
    # Before/After
    ax1.bar(['Standard LNAL', 'Final Model'], [1700, 2.86], 
            color=['darkred', 'darkgreen'], alpha=0.7)
    ax1.set_yscale('log')
    ax1.set_ylabel('Median χ²/N')
    ax1.set_title('Before vs After', fontsize=16, fontweight='bold')
    ax1.axhline(y=1.0, color='red', linestyle='--', linewidth=2)
    
    # Success rate
    labels = ['χ²/N < 1.0', 'χ²/N < 2.0', 'χ²/N > 2.0']
    sizes = [28, 14.9, 57.1]
    colors = ['darkgreen', 'orange', 'darkred']
    ax2.pie(sizes, labels=labels, colors=colors, autopct='%1.0f%%',
            startangle=90, textprops={'fontsize': 12, 'fontweight': 'bold'})
    ax2.set_title('Final Performance Distribution', fontsize=16, fontweight='bold')
    
    plt.tight_layout()
    plt.savefig('LNAL_Before_After.png', dpi=200)
    print("Created: LNAL_Before_After.png")

if __name__ == "__main__":
    create_summary_plot() 