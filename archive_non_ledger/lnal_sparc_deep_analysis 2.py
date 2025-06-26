"""
Deep analysis of SPARC rotation curves with LNAL model
Explores model improvements and residual patterns
"""

import numpy as np
import matplotlib.pyplot as plt
from scipy.optimize import curve_fit, differential_evolution
from scipy.stats import pearsonr, spearmanr
import pandas as pd
import os
import glob
from matplotlib.gridspec import GridSpec
import seaborn as sns
from scipy.interpolate import interp1d

# Physical constants
G = 4.302e-6  # kpc km^2 s^-2 M_sun^-1
PHI = (1 + np.sqrt(5)) / 2  # Golden ratio
a0 = 1.2e-10 * 3.086e13 / 1e3**2  # m/s^2 to kpc/s^2 = 3.7e-4 kpc/s^2

def lnal_transition(x, power=PHI):
    """LNAL transition function F(x) = (1 + exp(-x^φ))^(-1/φ)"""
    return np.power(1 + np.exp(-np.power(x, power)), -1/power)

def lnal_acceleration(g_newton, a0_scale=a0):
    """Apply LNAL correction to Newtonian acceleration"""
    return g_newton * lnal_transition(g_newton / a0_scale)

def load_galaxy_data(filename):
    """Load rotation curve data from SPARC file"""
    data = {}
    
    # Read header for distance
    with open(filename, 'r') as f:
        for line in f:
            if line.startswith('# Distance'):
                data['distance'] = float(line.split('=')[1].split('Mpc')[0].strip())
                break
    
    # Read data columns
    df = pd.read_csv(filename, comment='#', delim_whitespace=True,
                     names=['rad', 'vobs', 'verr', 'vgas', 'vdisk', 'vbul', 'sbdisk', 'sbbul'])
    
    # Clean data - remove invalid points
    mask = (df['rad'] > 0) & (df['vobs'] > 0) & (df['verr'] > 0)
    df = df[mask]
    
    data['df'] = df
    data['name'] = os.path.basename(filename).replace('_rotmod.dat', '')
    
    return data

def calculate_total_mass(r, vgas, vdisk, vbul):
    """Calculate total enclosed mass from velocity components"""
    vtot_sq = vgas**2 + vdisk**2 + vbul**2
    return vtot_sq * r / G

def fit_lnal_model(galaxy_data, fit_a0=False, fit_power=False):
    """Fit LNAL model to galaxy rotation curve"""
    df = galaxy_data['df']
    r = df['rad'].values
    vobs = df['vobs'].values
    verr = df['verr'].values
    
    # Calculate Newtonian prediction from components
    v_newton_sq = df['vgas']**2 + df['vdisk']**2 + df['vbul']**2
    g_newton = v_newton_sq / r
    
    if fit_a0 or fit_power:
        # Fit model parameters
        def model(r_vals, *params):
            if fit_a0 and fit_power:
                a0_fit, power_fit = params
                g_lnal = lnal_acceleration(g_newton, a0_fit)
                return np.sqrt(g_lnal * r_vals)
            elif fit_a0:
                a0_fit = params[0]
                g_lnal = lnal_acceleration(g_newton, a0_fit)
                return np.sqrt(g_lnal * r_vals)
            else:  # fit_power
                power_fit = params[0]
                g_lnal = g_newton * lnal_transition(g_newton / a0, power_fit)
                return np.sqrt(g_lnal * r_vals)
        
        # Initial guesses and bounds
        if fit_a0 and fit_power:
            p0 = [a0, PHI]
            bounds = ([a0/10, 1.0], [a0*10, 2.0])
        elif fit_a0:
            p0 = [a0]
            bounds = ([a0/10], [a0*10])
        else:
            p0 = [PHI]
            bounds = ([1.0], [2.0])
        
        try:
            popt, pcov = curve_fit(model, r, vobs, p0=p0, sigma=verr, 
                                 bounds=bounds, absolute_sigma=True)
            params = popt
        except:
            params = p0
    else:
        params = []
    
    # Calculate LNAL prediction
    if fit_a0 and fit_power:
        g_lnal = lnal_acceleration(g_newton, params[0])
    elif fit_a0:
        g_lnal = lnal_acceleration(g_newton, params[0])
    elif fit_power:
        g_lnal = g_newton * lnal_transition(g_newton / a0, params[0])
    else:
        g_lnal = lnal_acceleration(g_newton)
    
    v_lnal = np.sqrt(g_lnal * r)
    
    # Calculate residuals and chi-squared
    residuals = (vobs - v_lnal) / verr
    chi2 = np.sum(residuals**2)
    dof = len(vobs) - len(params)
    chi2_reduced = chi2 / dof
    
    results = {
        'r': r,
        'vobs': vobs,
        'verr': verr,
        'v_newton': np.sqrt(v_newton_sq),
        'v_lnal': v_lnal,
        'g_newton': g_newton,
        'g_lnal': g_lnal,
        'residuals': residuals,
        'chi2': chi2,
        'chi2_reduced': chi2_reduced,
        'params': params
    }
    
    return results

def analyze_residual_patterns(all_results):
    """Analyze patterns in residuals across all galaxies"""
    fig = plt.figure(figsize=(20, 16))
    gs = GridSpec(4, 4, figure=fig, hspace=0.3, wspace=0.3)
    
    # Collect all residual data
    all_residuals = []
    all_accelerations = []
    all_radii = []
    all_gas_fractions = []
    all_masses = []
    galaxy_properties = []
    
    for name, results in all_results.items():
        galaxy = results['galaxy']
        fit = results['fit_standard']
        df = galaxy['df']
        
        # Calculate properties
        total_mass = calculate_total_mass(fit['r'][-1], 
                                        df['vgas'].iloc[-1], 
                                        df['vdisk'].iloc[-1], 
                                        df['vbul'].iloc[-1])
        
        gas_fraction = np.mean(df['vgas']**2 / (df['vgas']**2 + df['vdisk']**2 + df['vbul']**2 + 1e-10))
        
        # Store data
        relative_residuals = (fit['vobs'] - fit['v_lnal']) / fit['v_lnal']
        all_residuals.extend(relative_residuals)
        all_accelerations.extend(fit['g_lnal'])
        all_radii.extend(fit['r'])
        all_gas_fractions.extend([gas_fraction] * len(fit['r']))
        all_masses.extend([np.log10(total_mass)] * len(fit['r']))
        
        galaxy_properties.append({
            'name': name,
            'mass': total_mass,
            'gas_fraction': gas_fraction,
            'chi2_reduced': fit['chi2_reduced'],
            'mean_residual': np.mean(relative_residuals),
            'std_residual': np.std(relative_residuals)
        })
    
    # Convert to arrays
    all_residuals = np.array(all_residuals)
    all_accelerations = np.array(all_accelerations)
    all_radii = np.array(all_radii)
    all_gas_fractions = np.array(all_gas_fractions)
    all_masses = np.array(all_masses)
    
    # 1. Residuals vs acceleration
    ax1 = fig.add_subplot(gs[0, 0])
    scatter = ax1.scatter(np.log10(all_accelerations), all_residuals * 100, 
                         c=all_gas_fractions, cmap='viridis', alpha=0.5, s=10)
    ax1.axhline(0, color='k', linestyle='--', alpha=0.5)
    ax1.set_xlabel('log(g_LNAL) [kpc/s²]')
    ax1.set_ylabel('Relative Residual (%)')
    ax1.set_title('Residuals vs LNAL Acceleration')
    plt.colorbar(scatter, ax=ax1, label='Gas Fraction')
    
    # 2. Residuals vs radius
    ax2 = fig.add_subplot(gs[0, 1])
    scatter2 = ax2.scatter(np.log10(all_radii), all_residuals * 100, 
                          c=all_masses, cmap='plasma', alpha=0.5, s=10)
    ax2.axhline(0, color='k', linestyle='--', alpha=0.5)
    ax2.set_xlabel('log(R) [kpc]')
    ax2.set_ylabel('Relative Residual (%)')
    ax2.set_title('Residuals vs Radius')
    plt.colorbar(scatter2, ax=ax2, label='log(M_total)')
    
    # 3. Histogram of residuals
    ax3 = fig.add_subplot(gs[0, 2])
    ax3.hist(all_residuals * 100, bins=50, alpha=0.7, edgecolor='black')
    ax3.axvline(0, color='k', linestyle='--', alpha=0.5)
    ax3.set_xlabel('Relative Residual (%)')
    ax3.set_ylabel('Count')
    ax3.set_title(f'Distribution of Residuals\nMean: {np.mean(all_residuals)*100:.2f}%')
    
    # 4. Galaxy properties correlation
    gdf = pd.DataFrame(galaxy_properties)
    ax4 = fig.add_subplot(gs[0, 3])
    ax4.scatter(gdf['gas_fraction'], gdf['mean_residual'] * 100, 
               s=50, alpha=0.7)
    ax4.set_xlabel('Gas Fraction')
    ax4.set_ylabel('Mean Residual (%)')
    ax4.set_title('Mean Residual vs Gas Fraction')
    
    # Fit linear relation
    mask = ~np.isnan(gdf['gas_fraction']) & ~np.isnan(gdf['mean_residual'])
    if np.sum(mask) > 10:
        z = np.polyfit(gdf['gas_fraction'][mask], gdf['mean_residual'][mask], 1)
        p = np.poly1d(z)
        x_fit = np.linspace(0, gdf['gas_fraction'].max(), 100)
        ax4.plot(x_fit, p(x_fit) * 100, 'r--', 
                label=f'δ = {z[1]*100:.2f} + {z[0]*100:.1f} × f_gas')
        ax4.legend()
    
    # 5. Chi-squared distribution
    ax5 = fig.add_subplot(gs[1, 0])
    ax5.hist(gdf['chi2_reduced'], bins=30, alpha=0.7, edgecolor='black')
    ax5.axvline(1.0, color='r', linestyle='--', alpha=0.5, label='χ²/ν = 1')
    ax5.set_xlabel('Reduced χ²')
    ax5.set_ylabel('Number of Galaxies')
    ax5.set_title(f'χ² Distribution\nMedian: {np.median(gdf["chi2_reduced"]):.2f}')
    ax5.legend()
    
    # 6. Residuals in different regimes
    ax6 = fig.add_subplot(gs[1, 1])
    
    # Define regimes
    deep_lnal = all_accelerations < 0.1 * a0
    transition = (all_accelerations >= 0.1 * a0) & (all_accelerations <= 10 * a0)
    newtonian = all_accelerations > 10 * a0
    
    regimes = ['Deep LNAL\n(g < 0.1a₀)', 'Transition\n(0.1a₀ < g < 10a₀)', 'Newtonian\n(g > 10a₀)']
    regime_residuals = [
        all_residuals[deep_lnal] * 100,
        all_residuals[transition] * 100,
        all_residuals[newtonian] * 100
    ]
    
    bp = ax6.boxplot(regime_residuals, labels=regimes, patch_artist=True)
    for patch in bp['boxes']:
        patch.set_facecolor('lightblue')
    ax6.axhline(0, color='k', linestyle='--', alpha=0.5)
    ax6.set_ylabel('Relative Residual (%)')
    ax6.set_title('Residuals by Regime')
    
    # 7. Test modified LNAL with different powers
    ax7 = fig.add_subplot(gs[1, 2])
    powers = np.linspace(1.0, 2.0, 21)
    mean_chi2 = []
    
    for power in powers:
        chi2_list = []
        for name, results in all_results.items():
            galaxy = results['galaxy']
            df = galaxy['df']
            r = df['rad'].values
            vobs = df['vobs'].values
            verr = df['verr'].values
            v_newton_sq = df['vgas']**2 + df['vdisk']**2 + df['vbul']**2
            g_newton = v_newton_sq / r
            
            # Calculate LNAL with modified power
            g_lnal = g_newton * lnal_transition(g_newton / a0, power)
            v_lnal = np.sqrt(g_lnal * r)
            
            chi2 = np.sum(((vobs - v_lnal) / verr)**2) / len(vobs)
            chi2_list.append(chi2)
        
        mean_chi2.append(np.median(chi2_list))
    
    ax7.plot(powers, mean_chi2, 'b-', linewidth=2)
    ax7.axvline(PHI, color='r', linestyle='--', alpha=0.5, label=f'φ = {PHI:.3f}')
    ax7.set_xlabel('Power in F(x)')
    ax7.set_ylabel('Median χ²/ν')
    ax7.set_title('Optimizing Transition Function Power')
    ax7.legend()
    ax7.grid(True, alpha=0.3)
    
    # 8. Test different a0 values
    ax8 = fig.add_subplot(gs[1, 3])
    a0_factors = np.logspace(-0.5, 0.5, 21)
    mean_chi2_a0 = []
    
    for factor in a0_factors:
        chi2_list = []
        for name, results in all_results.items():
            galaxy = results['galaxy']
            df = galaxy['df']
            r = df['rad'].values
            vobs = df['vobs'].values
            verr = df['verr'].values
            v_newton_sq = df['vgas']**2 + df['vdisk']**2 + df['vbul']**2
            g_newton = v_newton_sq / r
            
            # Calculate LNAL with modified a0
            g_lnal = lnal_acceleration(g_newton, a0 * factor)
            v_lnal = np.sqrt(g_lnal * r)
            
            chi2 = np.sum(((vobs - v_lnal) / verr)**2) / len(vobs)
            chi2_list.append(chi2)
        
        mean_chi2_a0.append(np.median(chi2_list))
    
    ax8.semilogx(a0_factors, mean_chi2_a0, 'g-', linewidth=2)
    ax8.axvline(1.0, color='r', linestyle='--', alpha=0.5, label='Standard a₀')
    ax8.set_xlabel('a₀ multiplication factor')
    ax8.set_ylabel('Median χ²/ν')
    ax8.set_title('Optimizing a₀')
    ax8.legend()
    ax8.grid(True, alpha=0.3)
    
    # 9. Recognition length analysis
    ax9 = fig.add_subplot(gs[2, 0])
    
    # Define recognition lengths
    l1 = 0.97  # kpc
    l2 = 24.3  # kpc
    
    # Categorize by radius
    inner = all_radii < l1
    middle = (all_radii >= l1) & (all_radii < l2)
    outer = all_radii >= l2
    
    categories = [f'r < {l1} kpc', f'{l1} < r < {l2} kpc', f'r > {l2} kpc']
    category_residuals = [
        all_residuals[inner] * 100,
        all_residuals[middle] * 100,
        all_residuals[outer] * 100
    ]
    
    bp2 = ax9.boxplot(category_residuals, labels=categories, patch_artist=True)
    for patch in bp2['boxes']:
        patch.set_facecolor('lightgreen')
    ax9.axhline(0, color='k', linestyle='--', alpha=0.5)
    ax9.set_ylabel('Relative Residual (%)')
    ax9.set_title('Residuals by Recognition Length')
    
    # 10. Surface density effects
    ax10 = fig.add_subplot(gs[2, 1])
    
    # Calculate surface densities at each point
    all_surface_densities = []
    for name, results in all_results.items():
        galaxy = results['galaxy']
        df = galaxy['df']
        sb_total = df['sbdisk'] + df['sbbul']
        all_surface_densities.extend(sb_total)
    
    all_surface_densities = np.array(all_surface_densities)
    mask = all_surface_densities > 0
    
    ax10.scatter(np.log10(all_surface_densities[mask]), 
                all_residuals[mask] * 100, alpha=0.3, s=5)
    ax10.set_xlabel('log(Surface Brightness) [L/pc²]')
    ax10.set_ylabel('Relative Residual (%)')
    ax10.set_title('Residuals vs Surface Density')
    ax10.axhline(0, color='k', linestyle='--', alpha=0.5)
    
    # 11. Improved model test - add screening length
    ax11 = fig.add_subplot(gs[2, 2])
    
    # Test model with exponential screening
    screening_lengths = np.logspace(0, 2, 11)  # 1 to 100 kpc
    mean_chi2_screen = []
    
    for L_screen in screening_lengths:
        chi2_list = []
        for name, results in all_results.items():
            galaxy = results['galaxy']
            df = galaxy['df']
            r = df['rad'].values
            vobs = df['vobs'].values
            verr = df['verr'].values
            v_newton_sq = df['vgas']**2 + df['vdisk']**2 + df['vbul']**2
            g_newton = v_newton_sq / r
            
            # LNAL with exponential screening
            screening_factor = 1 - np.exp(-r / L_screen)
            g_lnal = lnal_acceleration(g_newton) * screening_factor
            v_lnal = np.sqrt(g_lnal * r)
            
            chi2 = np.sum(((vobs - v_lnal) / verr)**2) / len(vobs)
            chi2_list.append(chi2)
        
        mean_chi2_screen.append(np.median(chi2_list))
    
    ax11.semilogx(screening_lengths, mean_chi2_screen, 'r-', linewidth=2)
    ax11.axhline(np.median(gdf['chi2_reduced']), color='b', linestyle='--', 
                 alpha=0.5, label='Standard LNAL')
    ax11.set_xlabel('Screening Length [kpc]')
    ax11.set_ylabel('Median χ²/ν')
    ax11.set_title('LNAL with Exponential Screening')
    ax11.legend()
    ax11.grid(True, alpha=0.3)
    
    # 12. Information overhead model
    ax12 = fig.add_subplot(gs[2, 3])
    
    # Fit overhead model: delta = delta_0 + alpha * f_gas
    gas_fracs = gdf['gas_fraction'].values
    mean_resids = gdf['mean_residual'].values
    
    mask = ~np.isnan(gas_fracs) & ~np.isnan(mean_resids)
    if np.sum(mask) > 10:
        from scipy.stats import linregress
        slope, intercept, r_value, p_value, std_err = linregress(
            gas_fracs[mask], mean_resids[mask])
        
        ax12.scatter(gas_fracs, mean_resids * 100, alpha=0.7, s=50)
        x_line = np.linspace(0, gas_fracs.max(), 100)
        y_line = (intercept + slope * x_line) * 100
        
        ax12.plot(x_line, y_line, 'r-', linewidth=2,
                 label=f'δ = {intercept*100:.2f}% + {slope*100:.1f}% × f_gas\n' + 
                       f'R² = {r_value**2:.3f}, p = {p_value:.3e}')
        
        ax12.set_xlabel('Gas Fraction')
        ax12.set_ylabel('Mean Residual (%)')
        ax12.set_title('Information Overhead Model')
        ax12.legend()
        ax12.grid(True, alpha=0.3)
    
    # 13. Velocity-dependent residuals
    ax13 = fig.add_subplot(gs[3, 0])
    all_velocities = []
    for name, results in all_results.items():
        fit = results['fit_standard']
        all_velocities.extend(fit['vobs'])
    all_velocities = np.array(all_velocities)
    
    ax13.scatter(all_velocities, all_residuals * 100, alpha=0.3, s=5)
    ax13.set_xlabel('Observed Velocity [km/s]')
    ax13.set_ylabel('Relative Residual (%)')
    ax13.set_title('Residuals vs Velocity')
    ax13.axhline(0, color='k', linestyle='--', alpha=0.5)
    
    # 14. Best and worst fits
    ax14 = fig.add_subplot(gs[3, 1:])
    
    # Sort by chi-squared
    sorted_galaxies = sorted(galaxy_properties, key=lambda x: x['chi2_reduced'])
    
    # Plot best and worst fits
    best_names = [sorted_galaxies[i]['name'] for i in range(3)]
    worst_names = [sorted_galaxies[-i]['name'] for i in range(1, 4)]
    
    colors = plt.cm.tab10(np.arange(6))
    
    for i, name in enumerate(best_names):
        results = all_results[name]
        fit = results['fit_standard']
        label = f'{name} (χ²/ν={sorted_galaxies[i]["chi2_reduced"]:.2f})'
        ax14.plot(fit['r'], fit['vobs'], 'o', color=colors[i], markersize=4, alpha=0.7)
        ax14.plot(fit['r'], fit['v_lnal'], '-', color=colors[i], linewidth=2, label=label)
    
    for i, name in enumerate(worst_names):
        results = all_results[name]
        fit = results['fit_standard']
        idx = len(sorted_galaxies) - i - 1
        label = f'{name} (χ²/ν={sorted_galaxies[idx]["chi2_reduced"]:.2f})'
        ax14.plot(fit['r'], fit['vobs'], 's', color=colors[i+3], markersize=4, alpha=0.7)
        ax14.plot(fit['r'], fit['v_lnal'], '--', color=colors[i+3], linewidth=2, label=label)
    
    ax14.set_xlabel('Radius [kpc]')
    ax14.set_ylabel('Velocity [km/s]')
    ax14.set_title('Best Fits (solid) and Worst Fits (dashed)')
    ax14.legend(loc='upper left', fontsize=8)
    ax14.set_xscale('log')
    ax14.set_xlim(0.1, 100)
    ax14.grid(True, alpha=0.3)
    
    plt.tight_layout()
    return fig, galaxy_properties

def create_improved_lnal_model():
    """Create improved LNAL model based on analysis"""
    fig, axes = plt.subplots(2, 2, figsize=(15, 12))
    
    # Test different functional forms
    x = np.logspace(-2, 2, 1000)
    
    # Standard LNAL
    f_standard = lnal_transition(x)
    
    # Modified with different powers
    f_mod1 = lnal_transition(x, power=1.5)
    f_mod2 = lnal_transition(x, power=1.7)
    
    # With screening
    L_screen = 10  # in units of a0
    f_screen = f_standard * (1 - np.exp(-x * L_screen))
    
    # With information overhead
    delta_0 = 0.005
    f_overhead = f_standard * (1 + delta_0)
    
    # Plot transition functions
    ax = axes[0, 0]
    ax.loglog(x, f_standard, 'k-', linewidth=2, label='Standard LNAL')
    ax.loglog(x, f_mod1, 'b--', linewidth=2, label='Power = 1.5')
    ax.loglog(x, f_mod2, 'r--', linewidth=2, label='Power = 1.7')
    ax.loglog(x, f_screen, 'g:', linewidth=2, label='With screening')
    ax.loglog(x, f_overhead, 'm-.', linewidth=2, label='With overhead')
    
    # Add asymptotic limits
    ax.loglog(x, x**0.5, 'k:', alpha=0.5, label='Deep LNAL limit')
    ax.loglog(x, np.ones_like(x), 'k:', alpha=0.5, label='Newtonian limit')
    
    ax.set_xlabel('x = g_N / a₀')
    ax.set_ylabel('F(x)')
    ax.set_title('Transition Function Variations')
    ax.legend()
    ax.grid(True, alpha=0.3)
    ax.set_xlim(0.01, 100)
    ax.set_ylim(0.1, 2)
    
    # Plot effective acceleration
    ax2 = axes[0, 1]
    g_eff_standard = x * f_standard
    g_eff_mod1 = x * f_mod1
    g_eff_screen = x * f_screen
    
    ax2.loglog(x, g_eff_standard, 'k-', linewidth=2, label='Standard')
    ax2.loglog(x, g_eff_mod1, 'b--', linewidth=2, label='Power = 1.5')
    ax2.loglog(x, g_eff_screen, 'g:', linewidth=2, label='With screening')
    ax2.loglog(x, x, 'k:', alpha=0.5, label='Newtonian')
    ax2.loglog(x, x**0.5, 'k:', alpha=0.5, label='Deep LNAL')
    
    ax2.set_xlabel('g_N / a₀')
    ax2.set_ylabel('g_LNAL / a₀')
    ax2.set_title('Effective Acceleration')
    ax2.legend()
    ax2.grid(True, alpha=0.3)
    
    # Plot derivatives (to check smoothness)
    ax3 = axes[1, 0]
    
    # Numerical derivatives
    df_dx = np.gradient(f_standard, x)
    df_dx_mod = np.gradient(f_mod1, x)
    
    ax3.semilogx(x, df_dx, 'k-', linewidth=2, label='Standard LNAL')
    ax3.semilogx(x, df_dx_mod, 'b--', linewidth=2, label='Power = 1.5')
    
    ax3.set_xlabel('x = g_N / a₀')
    ax3.set_ylabel('dF/dx')
    ax3.set_title('Derivative of Transition Function')
    ax3.legend()
    ax3.grid(True, alpha=0.3)
    
    # Plot second derivatives (curvature)
    ax4 = axes[1, 1]
    
    d2f_dx2 = np.gradient(df_dx, x)
    d2f_dx2_mod = np.gradient(df_dx_mod, x)
    
    ax4.semilogx(x, d2f_dx2, 'k-', linewidth=2, label='Standard LNAL')
    ax4.semilogx(x, d2f_dx2_mod, 'b--', linewidth=2, label='Power = 1.5')
    
    ax4.set_xlabel('x = g_N / a₀')
    ax4.set_ylabel('d²F/dx²')
    ax4.set_title('Curvature of Transition Function')
    ax4.legend()
    ax4.grid(True, alpha=0.3)
    ax4.axhline(0, color='gray', linestyle=':', alpha=0.5)
    
    plt.tight_layout()
    return fig

def main():
    """Main analysis pipeline"""
    print("Loading SPARC rotation curve data...")
    
    # Load all galaxy data
    data_files = glob.glob('Rotmod_LTG/*_rotmod.dat')
    # Filter out duplicates (files with ' 2' in name)
    data_files = [f for f in data_files if ' 2' not in f]
    
    all_results = {}
    
    print(f"Found {len(data_files)} galaxies")
    
    for i, filename in enumerate(data_files):
        if (i + 1) % 20 == 0:
            print(f"Processing galaxy {i+1}/{len(data_files)}...")
        
        try:
            # Load galaxy
            galaxy = load_galaxy_data(filename)
            
            # Skip if too few data points
            if len(galaxy['df']) < 5:
                continue
            
            # Fit different models
            fit_standard = fit_lnal_model(galaxy, fit_a0=False, fit_power=False)
            fit_a0 = fit_lnal_model(galaxy, fit_a0=True, fit_power=False)
            fit_power = fit_lnal_model(galaxy, fit_a0=False, fit_power=True)
            
            all_results[galaxy['name']] = {
                'galaxy': galaxy,
                'fit_standard': fit_standard,
                'fit_a0': fit_a0,
                'fit_power': fit_power
            }
            
        except Exception as e:
            print(f"Error processing {filename}: {e}")
            continue
    
    print(f"\nSuccessfully processed {len(all_results)} galaxies")
    
    # Create analysis plots
    print("\nAnalyzing residual patterns...")
    fig1, galaxy_props = analyze_residual_patterns(all_results)
    fig1.savefig('lnal_sparc_residual_analysis.png', dpi=150, bbox_inches='tight')
    print("Saved: lnal_sparc_residual_analysis.png")
    
    # Create improved model plots
    print("\nTesting improved models...")
    fig2 = create_improved_lnal_model()
    fig2.savefig('lnal_improved_models.png', dpi=150, bbox_inches='tight')
    print("Saved: lnal_improved_models.png")
    
    # Save summary statistics
    gdf = pd.DataFrame(galaxy_props)
    
    print("\n" + "="*60)
    print("SUMMARY STATISTICS")
    print("="*60)
    print(f"Total galaxies analyzed: {len(gdf)}")
    print(f"Mean χ²/ν: {gdf['chi2_reduced'].mean():.3f} ± {gdf['chi2_reduced'].std():.3f}")
    print(f"Median χ²/ν: {gdf['chi2_reduced'].median():.3f}")
    print(f"Galaxies with χ²/ν < 2: {(gdf['chi2_reduced'] < 2).sum()} ({(gdf['chi2_reduced'] < 2).sum()/len(gdf)*100:.1f}%)")
    print(f"\nMean relative residual: {gdf['mean_residual'].mean()*100:.3f}%")
    print(f"All residuals positive: {(gdf['mean_residual'] > 0).all()}")
    
    # Fit overhead model
    mask = ~gdf['gas_fraction'].isna()
    if mask.sum() > 10:
        from scipy.stats import linregress
        slope, intercept, r_value, p_value, std_err = linregress(
            gdf['gas_fraction'][mask], gdf['mean_residual'][mask])
        
        print(f"\nInformation overhead model:")
        print(f"δ = {intercept*100:.3f}% + {slope*100:.2f}% × f_gas")
        print(f"R² = {r_value**2:.3f}, p-value = {p_value:.3e}")
    
    # Save detailed results
    gdf.to_csv('lnal_sparc_galaxy_properties.csv', index=False)
    print("\nSaved: lnal_sparc_galaxy_properties.csv")
    
    # Test statistical significance of improvements
    print("\n" + "="*60)
    print("MODEL COMPARISON")
    print("="*60)
    
    chi2_standard = []
    chi2_fitted_a0 = []
    chi2_fitted_power = []
    
    for name, results in all_results.items():
        chi2_standard.append(results['fit_standard']['chi2_reduced'])
        chi2_fitted_a0.append(results['fit_a0']['chi2_reduced'])
        chi2_fitted_power.append(results['fit_power']['chi2_reduced'])
    
    chi2_standard = np.array(chi2_standard)
    chi2_fitted_a0 = np.array(chi2_fitted_a0)
    chi2_fitted_power = np.array(chi2_fitted_power)
    
    print(f"Standard LNAL - Median χ²/ν: {np.median(chi2_standard):.3f}")
    print(f"Fitted a₀ - Median χ²/ν: {np.median(chi2_fitted_a0):.3f}")
    print(f"Fitted power - Median χ²/ν: {np.median(chi2_fitted_power):.3f}")
    
    # Wilcoxon signed-rank test
    from scipy.stats import wilcoxon
    
    stat1, p1 = wilcoxon(chi2_standard, chi2_fitted_a0)
    stat2, p2 = wilcoxon(chi2_standard, chi2_fitted_power)
    
    print(f"\nWilcoxon test - Standard vs Fitted a₀: p = {p1:.3e}")
    print(f"Wilcoxon test - Standard vs Fitted power: p = {p2:.3e}")
    
    return all_results, gdf

if __name__ == "__main__":
    all_results, galaxy_properties = main() 