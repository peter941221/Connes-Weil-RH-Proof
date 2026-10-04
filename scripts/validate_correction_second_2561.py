"""Independent differentiation and envelope controls for the 2561 probe."""
from fractions import Fraction as F
import hashlib
import json
import mpmath as mp
from flint import ctx
import price_correction_second_2561 as p


def m(value):
    value = F(value)
    return mp.mpf(value.numerator)/value.denominator


def arb_mid(value):
    return m(str(value.mid().fmpq()))


def controls():
    ctx.prec = 192
    mp.mp.dps = 90
    families = p.load_families()
    checks, envelope_checks, max_scaled = 0, 0, mp.mpf(0)
    wrong_convention_detected = False
    for index in (0,15,29):
        f = families[index]
        radius, theta = m(f['r']), m(f['theta_exact'])
        def atom(x):
            return mp.exp(-30/(1-(x/radius)**2)+1j*theta*x)
        for sigma in (F(-1,2),F(1,2)):
            for fraction in (F(-3,5),F(0),F(2,5)):
                x = f['r']*fraction
                got = p.jets(f,x,sigma,4)
                for order in range(5):
                    expected = mp.exp(m(sigma)*m(x))*sum(
                        mp.binomial(order,j)*m(sigma)**(order-j)*mp.diff(atom,m(x),j+2)
                        for j in range(order+1))
                    observed = mp.mpc(arb_mid(got[order].real),arb_mid(got[order].imag))
                    scaled = abs(observed-expected)/(abs(expected)+mp.mpf('1e-70'))
                    assert scaled < mp.mpf('1e-45'),(index,sigma,x,order,str(scaled))
                    max_scaled = max(max_scaled,scaled)
                    checks += 1
                wrong = mp.diff(lambda t: mp.exp(m(sigma)*t)*atom(t),m(x),2)
                correct = mp.exp(m(sigma)*m(x))*mp.diff(atom,m(x),2)
                wrong_convention_detected |= abs(wrong-correct)>mp.mpf('1e-8')*abs(correct)
            for a,b in ((-f['r'], -f['r']*F(99,100)),
                        (-f['r']/100,f['r']/100),
                        (f['r']*F(99,100),f['r']*F(101,100))):
                bound = p.envelope(f,a,b,sigma)
                for t in (F(0),F(1,4),F(1,2),F(3,4),F(1)):
                    value = abs(p.jets(f,a+(b-a)*t,sigma,4)[4])
                    assert value <= bound,(index,a,b,t)
                    envelope_checks += 1
        for x in (-f['r'],f['r'],2*f['r']):
            assert all(z == 0 for z in p.jets(f,x,F(1,2),4))
    assert wrong_convention_detected
    return dict(status='INDEPENDENT_DERIVATIVE_CONTROLS_PASS',derivative_checks=checks,
                envelope_sample_checks=envelope_checks,max_scaled_error=str(max_scaled),
                wrong_weighted_derivative_detected=True,
                envelope_samples_are_not_integral_certificates=True)


if __name__ == '__main__':
    result = controls()
    result['source_sha256'] = {str(path.relative_to(p.ROOT)):hashlib.sha256(path.read_bytes()).hexdigest()
        for path in (p.ROOT/'scripts/price_correction_second_2561.py',p.ROOT/'scripts/validate_correction_second_2561.py')}
    (p.ROOT/'results/2561_correction_controls.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result),flush=True)
