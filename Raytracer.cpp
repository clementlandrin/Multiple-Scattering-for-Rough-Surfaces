// Raytracer.cpp : Ce fichier contient la fonction 'main'. L'exécution du programme commence et se termine à cet endroit.
//

#include "pch.h"

#include <math.h>
#include <stdlib.h>
#include <stdio.h>
#include <vector>
#include <iostream>
#include <random>
#include<time.h> 

#define M_PI 3.14159
#define NUMBER_GROOVE_SAMPLING 10
#define MAX_DEPTH 5
#define NB_SECONDARY_RAY 0

#define MAX_BOUNCES 1

#define PAPER_ROUGHNESS 0.00001

#define NUMBER_SAMPLES 10

int numberk = 0;
int number = 0;

std::default_random_engine generator;
std::normal_distribution<double> distribution(0.0, PAPER_ROUGHNESS);

std::default_random_engine bernoulli_generator;
std::bernoulli_distribution bernoulli; 

double min(double x, double y)
{
	return x < y ? x : y;
}

double max(double x, double y)
{
	return x > y ? x : y;
}

struct Vec
{
	double x, y, z;
	Vec(double x_ = 0, double y_ = 0, double z_ = 0)
	{
		x = x_;
		y = y_;
		z = z_;
	}
	Vec operator+(const Vec &b) const { return Vec(x + b.x, y + b.y, z + b.z); }
	Vec operator-(const Vec &b) const { return Vec(x - b.x, y - b.y, z - b.z); }
	Vec operator*(double b) const { return Vec(x * b, y * b, z * b); }
	Vec operator*(Vec u) const { return Vec(x * u.x, y * u.y, z * u.z); }
	Vec operator/(double b) const { return Vec(x / b, y / b, z / b); }
	Vec mult(const Vec &b) const { return Vec(x * b.x, y * b.y, z * b.z); }
	Vec &normalize() { return *this = *this * (1 / sqrt(x * x + y * y + z * z)); }
	double dot(const Vec &b) const { return x * b.x + y * b.y + z * b.z; }
	Vec cross(Vec &b) { return Vec(y * b.z - z * b.y, z * b.x - x * b.z, x * b.y - y * b.x); }
};
Vec operator*(double b, Vec const &o) { return Vec(o.x * b, o.y * b, o.z * b); }

void generateRandomPointOnSphere(double &theta, double &phi)
{
	double x = (double)(rand()) / RAND_MAX;
	double y = (double)(rand()) / RAND_MAX;
	theta = x * 2.0 * M_PI;
	phi = acos(min(1.0, min(-1.0, 2.0 * y - 1.0)));
}
Vec randomSampleOnSphere()
{
	double theta, phi;
	generateRandomPointOnSphere(theta, phi);
	return Vec(cos(theta) * cos(phi), sin(theta) * cos(phi), sin(phi));
}
Vec randomSampleOnHemisphere(Vec const &upDirection)
{
	Vec r = randomSampleOnSphere();
	if (r.dot(upDirection) > 0.0)
		return r;
	return -1.0 * r;
}

struct Ray
{
	Vec o, d;
	Ray(Vec o_, Vec d_) : o(o_), d(d_)
	{
		d.normalize();
	}
};

enum Refl_t
{
	DIFFUSE,
	MIRROR,
	GLASS,
	EMMISSIVE,
	ROUGH
}; // material types, used in radiance()

struct Sphere
{
	double radius; // radius
	Vec p, e, c;   // position, emission, color
	Refl_t refl;   // reflection type (DIFFuse, SPECular, REFRactive)
	float roughness;
	float kd;
	float metallic;
	Sphere(double rad_, Vec p_, Vec e_, Vec c_, Refl_t refl_, float metallic_, float roughness_, float kd_) : radius(rad_), p(p_), e(e_), c(c_), refl(refl_), metallic(metallic_), roughness(roughness_), kd(kd_) {}

	double intersect(const Ray &r) const
	{ // returns distance, 0 if nohit
		// TODO
		Vec oc = r.o - p;
		double sa = 1.0;
		double sb = 2.0 * oc.dot(r.d);
		double sc = oc.dot(oc) - radius * radius;

		double delta = sb * sb - 4.0 * sa * sc;
		if (delta < 0.0)
			return 0.0; // no solution

		double deltaSqrt = sqrt(delta);
		double lambda1 = (-sb - deltaSqrt) / (2.0 * sa);
		double lambda2 = (-sb + deltaSqrt) / (2.0 * sa);
		if (lambda1 < lambda2 && lambda1 >= 0.0)
			return lambda1;
		if (lambda2 >= 0.0)
			return lambda2;
		return 0.0;
	}

	Vec randomSample() const
	{
		return p + radius * randomSampleOnSphere();
	}
};

// Scene :
std::vector<Sphere> spheres;
std::vector<unsigned int> lights;
// lights is the whole set of emissive objects

inline double clamp(double x) { return x < 0 ? 0 : x > 1 ? 1 : x; }
inline double clamp(double x, double min, double max)
{
	if (x < min)
		x = min;
	else if (x > max)
		x = max;
	return x;
}
inline bool intersectScene(const Ray &r, double &t, int &id)
{
	double d, inf = t = 1e20;
	for (int i = 0; i < spheres.size(); ++i)
		if ((d = spheres[i].intersect(r)) && d < t)
		{
			t = d;
			id = i;
		}
	return t < inf;
}

double computeGeometricTerm(const Vec &n, const Vec &i, const Vec &s, bool kReflections)
{
	double thetav = acos(n.dot(s));
	double thetai = acos(i.dot(n));
	double thetaiortho = - thetai + M_PI / 2.0;

	int k = floor((M_PI + 2 * thetai) / thetav) + 1;
	double thetak = k * thetav - thetav / 2.0;
	double thetakMinus1 = (k - 1) * thetav - thetav / 2.0;

	double fk = cos(abs(thetai - thetak));
	double fa = cos(abs(thetai - thetav));

	if (!kReflections)
	{
		return abs((fa - fk) / fa);
	}
	else
	{
		double fb = max(cos(abs(thetai + thetav)), 0.0);
		return abs((fk - fb) / fa);
	}
}

// OK
int sampleK(const double GkMinus1, const double Gk)
{
	double p = Gk / (GkMinus1 + Gk);
	int k;

	double r = ((double)rand() / (RAND_MAX));
	if (r < p)
	{
		k = 1;
	}
	else
	{
		k = 0;
	}

	return k;
}

// OK
Vec computeOutputDirection(Vec &n, const Vec &s, Vec &i, const double thetai, const double thetav, const int k, const bool kReflections)
{
	double thetao = - pow(-1, k - 1 + kReflections) * (thetai + M_PI - (k - 1 + kReflections) * thetav);
	return (cos(thetao) * n + sin(thetao) * (i.cross(n)).cross(n).normalize()).normalize();
}

// OK ?
Vec sampleGrooveNormal(const Vec &n)
{
	double theta = std::acos(n.z);
	double phi = std::atan2(n.y, n.x);

	double deltaTheta = distribution(generator);
	double deltaPhi = distribution(generator);

	theta += deltaTheta;
	phi += deltaPhi;

	return Vec(std::sin(theta) * std::cos(phi), std::sin(theta) * std::sin(phi), std::cos(theta));
}

double fresnelTerm(double udotv, double metallic)
{
	return metallic + (1 - metallic)*pow(1 - max(0, udotv), 5);
}

double distributionTerm(Vec u, Vec v, double roughness)
{
	return pow(roughness, 2) / (M_PI * pow((1 + (pow(roughness, 2) - 1) * pow(u.dot(v), 2)), 2));
}

double cookTorranceBRDF(const Vec &wi, const Vec &n, const Vec &wo, const double metallic, const double roughness, const double kd)
{
	Vec wh = (wi + wo).normalize();
	double F = metallic + (1 - metallic)*pow(1 - max(0, wi.dot(wh)), 5);
	double D = pow(roughness, 2) / (M_PI * pow((1 + (pow(roughness, 2) - 1) * pow(n.dot(wh), 2)), 2));
	double Gi = 2 * n.dot(wi) / (n.dot(wi) + sqrt(pow(roughness, 2) + (1 - pow(roughness, 2)) * pow(n.dot(wi), 2)));
	double Go = 2 * n.dot(wo) / (n.dot(wo) + sqrt(pow(roughness, 2) + (1 - pow(roughness, 2)) * pow(n.dot(wo), 2)));
	double G = Gi * Go;
	double fs = D * F * G / (4 * n.dot(wi) * n.dot(wo));
	return fs + kd;
}

double brdf(const Vec &s, const Vec &wi, const Vec &n, const Vec &wo, const double thetav, const double G, const int number_bounces, const double roughness, const double metallic)
{
	Vec wh = (wi + wo).normalize();
	const double thetad = wh.dot(wi);
	const double thetah = wh.dot(n);

	const double thetas = (M_PI - thetav) / 2.0;

	const double thetai = wi.dot(n);

	double D = distributionTerm(s, wh, roughness);

	double sum = 0.0;

	for (int k = 1; k <= MAX_BOUNCES; k++)
	{
		double product = 1.0;
		for (int j = 1; j <= k; j++)
		{
			double F = fresnelTerm(abs(thetai + thetas * pow(-1.0, j)), metallic); 
			product *= F * D * G * wi.dot(s); // * wi.dot(s) ?
		}
		sum += sin(thetas) / (double)(k * sin(thetah)) * product / (4.0 * cos(thetad) * wi.dot(n) * wo.dot(n));
	}

	return sum;
}

Vec refract(const Vec &I, const Vec &N, const float &ior)
{
	float cosi = clamp(-1, 1, I.dot(N));
	float etai = 1, etat = ior;
	Vec n = N;
	if (cosi < 0)
		cosi = -cosi;
	else
	{
		std::swap(etai, etat);
		n = -1.0 * N;
	}
	float eta = etai / etat;
	float k = 1 - eta * eta * (1 - cosi * cosi);
	return k < 0 ? 0 : eta * I + (eta * cosi - sqrtf(k)) * n;
}

Vec radiance(const Ray &r, int depth, bool hit_only_lights = false)
{
	double t;   // distance to intersection
	int id = 0; // id of intersected object
	if (!intersectScene(r, t, id))
		return Vec(); // if miss, return black

	const Sphere &obj = spheres[id]; // the hit object

	Vec x = r.o + r.d * t,           // the hit position
		n = (x - obj.p).normalize(), // the normal of the object at the hit
		f = obj.c;                   // the color of the object at the hit

	if (n.dot(r.d) > 0.0)
		n = -1.0 * n;

	if (++depth > MAX_DEPTH)
	{
		return Vec(); // we limit the number of rebounds in the scene
	}

	if (obj.refl == EMMISSIVE)
	{ // we hit a light
		return obj.e;
	}

	if (hit_only_lights)
	{
		return Vec(0.0, 0.0, 0.0);
	}

	if (obj.refl == ROUGH)
	{ // Ideal DIFFUSE reflection
		Vec rad = Vec(0.0, 0.0, 0.0);
		Vec wi = -1.0 * r.d;

		for (unsigned int i = 0; i < NUMBER_GROOVE_SAMPLING; i++)
		{
			const Vec grooveNormal = sampleGrooveNormal(n);


			/*const double GkMinus1 = computeGeometricTerm(n, wi, grooveNormal, false);
			const double Gk = computeGeometricTerm(n, wi, grooveNormal, true);
			
			double thetav = acos(n.dot(grooveNormal));
			double thetai = acos(wi.dot(n));

			const int k = floor((M_PI + 2 * thetai) / thetav) + 1;
			const int kReflections = sampleK(GkMinus1, Gk);
			const double G = kReflections == 0 ? GkMinus1 : Gk;

			const Vec wo = computeOutputDirection(n, grooveNormal, wi, thetai, thetav, k, kReflections);*/

			for (unsigned int lightIt = 0; lightIt < lights.size(); ++lightIt)
			{
				const Sphere &light = spheres[lights[lightIt]];

				// TODO
				const Vec dirToLight = (light.randomSample() - x).normalize();
				const Ray &toLight = Ray(x + 0.0001 * dirToLight, dirToLight);
				int idTemp;
				double tTemp;
				if (intersectScene(toLight, tTemp, idTemp))
				{
					if (idTemp == lights[lightIt])
					{
						const Vec Li = light.e;
						rad = rad + Li.mult(obj.c) * cookTorranceBRDF(wi, grooveNormal, toLight.d, obj.metallic, obj.roughness, obj.kd) * (grooveNormal.dot(toLight.d)) / (NB_SECONDARY_RAY + 1) / NUMBER_GROOVE_SAMPLING;
					}
				}
			}
		}

		return rad;
	}
	else if (obj.refl == DIFFUSE)
	{ // Ideal DIFFUSE reflection
		// We shoot rays towards all lights:
		Vec rad;
		Vec wi = -1.0 * r.d;
		for (unsigned int lightIt = 0; lightIt < lights.size(); ++lightIt)
		{
			const Sphere &light = spheres[lights[lightIt]];

			// TODO
			const Vec dirToLight = (light.randomSample() - x).normalize();
			const Ray &toLight = Ray(x + 0.0001 * dirToLight, dirToLight);
			int idTemp;
			double tTemp;
			if (intersectScene(toLight, tTemp, idTemp))
			{
				if (idTemp == lights[lightIt])
				{
					const Vec Li = light.e;
					rad = rad + Li.mult(obj.c) * cookTorranceBRDF(-1.0 * r.d, n, toLight.d, obj.metallic, obj.roughness, obj.kd) * (n.dot(toLight.d)) / (NB_SECONDARY_RAY + 1);
				}
			}
		}

		// TODO : add secondary rays:
		for (unsigned int i = 0; i < NB_SECONDARY_RAY; i++)
		{
			const Vec newDir = randomSampleOnHemisphere(n).normalize();
			const Ray &newRay = Ray(x + 0.0001 * newDir, newDir);
			rad = rad + radiance(newRay, depth) * cookTorranceBRDF(-1.0 * r.d, n, newDir, obj.metallic, obj.roughness, obj.kd) * (n.dot(newRay.d)) / (NB_SECONDARY_RAY+1); // FIXME : Have to be normalized
		}

		return rad;
	}
	else if (obj.refl == MIRROR)
	{ // Ideal SPECULAR reflection
		// TODO
		Vec dirToReflected = r.d - 2 * n * (r.d.dot(n));
		const Ray &toReflected = Ray(x + 0.0001 * dirToReflected, dirToReflected);

		return radiance(toReflected, depth).mult(obj.c);
	}
	else if (obj.refl == GLASS)
	{ // Ideal SPECULAR refraction
		// TODO

		Vec dirToRefracted = refract(r.d, n, 1.500);
		const Ray &toReflected = Ray(x + 0.0001 * dirToRefracted, dirToRefracted);

		return radiance(toReflected, depth).mult(obj.c);
		return Vec();
	}

	return Vec();
}


int main(int argc, char *argv[])
{
	srand(time(0));

	int w = 1024, h = 768, samps = NUMBER_SAMPLES; // # samples
	Ray cam(Vec(50, 52, 295.6), Vec(0, -0.05, -1).normalize());   // camera center and direction
	Vec cx = Vec(w * .5135 / h), cy = (cx.cross(cam.d)).normalize() * .5135, *pixelsColor = new Vec[w * h];

	// setup scene:
	spheres.push_back(Sphere(1e5, Vec(1e5 + 1, 40.8, 81.6), Vec(0, 0, 0), Vec(.75, .25, .25), DIFFUSE, 0.3, 0.0, 0.5));   //Left
	spheres.push_back(Sphere(1e5, Vec(-1e5 + 99, 40.8, 81.6), Vec(0, 0, 0), Vec(.25, .25, .75), DIFFUSE, 0.2, 0.8, 0.5)); //Rght
	spheres.push_back(Sphere(1e5, Vec(50, 40.8, 1e5), Vec(0, 0, 0), Vec(.75, .75, .75), DIFFUSE, 1.0, 0.0, 0.5));         //Back
	spheres.push_back(Sphere(1e5, Vec(50, 40.8, -1e5 + 170), Vec(0, 0, 0), Vec(0, 0, 0), DIFFUSE, 0.2, 0.8, 0.5));        //Front
	spheres.push_back(Sphere(1e5, Vec(50, 1e5, 81.6), Vec(0, 0, 0), Vec(.75, .75, .75), DIFFUSE, 1.0, 0.0, 0.5));         //Bottom
	spheres.push_back(Sphere(1e5, Vec(50, -1e5 + 81.6, 81.6), Vec(0, 0, 0), Vec(.75, .75, .75), DIFFUSE, 0.5, 0.5, 0.5)); //Top
	spheres.push_back(Sphere(16.5, Vec(27, 16.5, 78), Vec(0, 0, 0), Vec(0.75, 0.75, 0.75), DIFFUSE, 0.7, 0.3, 0.0));         //Cook-Torrance sphere
	spheres.push_back(Sphere(16.5, Vec(73, 16.5, 78), Vec(0, 0, 0), Vec(0.75, 0.75, 0.75), ROUGH, 0.7, 0.3, 0.0));         //Paper's BRDF sphere
	spheres.push_back(Sphere(0.5, Vec(50, 70, 100), Vec(1, 1, 1), Vec(0, 0, 0), EMMISSIVE, 0.0, 0.0, 0.0));                  //Light
	lights.push_back(8);

	// ray trace:
	for (int y = 0; y < h; y++)
	{ // Loop over image rows
		fprintf(stderr, "\rRendering (%d spp) %5.2f%%", samps * 4, 100. * y / (h - 1));
		for (unsigned short x = 0; x < w; x++)
		{ // Loop cols
			Vec r(0, 0, 0);
			for (unsigned int sampleIt = 0; sampleIt < samps; ++sampleIt)
			{
				double dx = ((double)(rand()) / RAND_MAX);
				double dy = ((double)(rand()) / RAND_MAX);
				Vec d = cx * ((x + dx) / w - .5) +
					cy * ((y + dy) / h - .5) + cam.d;
				r = r + radiance(Ray(cam.o + d * 140, d.normalize()), 0) * (1. / samps);
			}

			pixelsColor[x + (h - 1 - y) * w] = pixelsColor[x + (h - 1 - y) * w] + Vec(clamp(r.x), clamp(r.y), clamp(r.z));
		} // Camera rays are pushed ^^^^^ forward to start in interior
	}

	// save image:
	FILE *f;
	errno_t err = fopen_s(&f, "image.ppm", "w"); // Write image to PPM file.

	fprintf(f, "P3\n%d %d\n%d\n", w, h, 255);
	for (int i = 0; i < w * h; i++)
		fprintf(f, "%d %d %d ", (int)(pixelsColor[i].x * 255), (int)(pixelsColor[i].y * 255), (int)(pixelsColor[i].z * 255));
	fclose(f);
}
